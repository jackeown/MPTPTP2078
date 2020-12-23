%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:46 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 445 expanded)
%              Number of leaves         :   34 ( 164 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 (1034 expanded)
%              Number of equality atoms :   41 ( 263 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_mcart_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_88,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_103,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
      & v1_relat_1(B)
      & v4_relat_1(B,A)
      & v5_relat_1(B,A)
      & v1_funct_1(B)
      & v1_funct_2(B,A,A)
      & v3_funct_2(B,A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_funct_2)).

tff(c_22,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_1'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( v1_xboole_0(k2_zfmisc_1(A_2,B_3))
      | ~ v1_xboole_0(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_341,plain,(
    ! [C_56,B_57,A_58] :
      ( ~ v1_xboole_0(C_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(C_56))
      | ~ r2_hidden(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_357,plain,(
    ! [A_58] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_58,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_341])).

tff(c_412,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_416,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_412])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_58,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50])).

tff(c_52,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1003,plain,(
    ! [B_103,C_104,A_105] :
      ( k1_xboole_0 = B_103
      | v1_funct_2(C_104,A_105,B_103)
      | k1_relset_1(A_105,B_103,C_104) != A_105
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1015,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_1003])).

tff(c_1026,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1015])).

tff(c_1027,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1026])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1072,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_2])).

tff(c_1074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_416,c_1072])).

tff(c_1077,plain,(
    ! [A_106] : ~ r2_hidden(A_106,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_1082,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_1077])).

tff(c_99,plain,(
    ! [A_35] :
      ( v1_xboole_0(k1_relat_1(A_35))
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_106,plain,(
    ! [A_38] :
      ( k1_relat_1(A_38) = k1_xboole_0
      | ~ v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_99,c_4])).

tff(c_114,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_106])).

tff(c_1100,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1082,c_1082,c_114])).

tff(c_1190,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_relset_1(A_110,B_111,C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1202,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_1190])).

tff(c_1205,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1100,c_52,c_1202])).

tff(c_1218,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_52])).

tff(c_10,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    ! [A_23] :
      ( v1_funct_2(k1_xboole_0,A_23,k1_xboole_0)
      | k1_xboole_0 = A_23
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_23,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_62,plain,(
    ! [A_23] :
      ( v1_funct_2(k1_xboole_0,A_23,k1_xboole_0)
      | k1_xboole_0 = A_23
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_24])).

tff(c_397,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_12,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_143,plain,(
    ! [A_42] : m1_subset_1('#skF_2'(A_42),k1_zfmisc_1(k2_zfmisc_1(A_42,A_42))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_147,plain,(
    m1_subset_1('#skF_2'(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_143])).

tff(c_345,plain,(
    ! [A_58] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_58,'#skF_2'(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_147,c_341])).

tff(c_358,plain,(
    ! [A_59] : ~ r2_hidden(A_59,'#skF_2'(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_345])).

tff(c_363,plain,(
    '#skF_2'(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_358])).

tff(c_365,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_147])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_397,c_365])).

tff(c_405,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1085,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1082,c_1082,c_405])).

tff(c_1346,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_1205,c_1085])).

tff(c_1215,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_1082])).

tff(c_28,plain,(
    ! [C_25,B_24] :
      ( v1_funct_2(C_25,k1_xboole_0,B_24)
      | k1_relset_1(k1_xboole_0,B_24,C_25) != k1_xboole_0
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_60,plain,(
    ! [C_25,B_24] :
      ( v1_funct_2(C_25,k1_xboole_0,B_24)
      | k1_relset_1(k1_xboole_0,B_24,C_25) != k1_xboole_0
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_28])).

tff(c_1370,plain,(
    ! [C_122,B_123] :
      ( v1_funct_2(C_122,'#skF_3',B_123)
      | k1_relset_1('#skF_3',B_123,C_122) != '#skF_3'
      | ~ m1_subset_1(C_122,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_1215,c_1215,c_1215,c_60])).

tff(c_2144,plain,(
    ! [B_175] :
      ( v1_funct_2('#skF_3','#skF_3',B_175)
      | k1_relset_1('#skF_3',B_175,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_1346,c_1370])).

tff(c_1219,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_58])).

tff(c_2149,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_2144,c_1219])).

tff(c_2159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1218,c_2149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:56:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.58  
% 3.62/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.59  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.62/1.59  
% 3.62/1.59  %Foreground sorts:
% 3.62/1.59  
% 3.62/1.59  
% 3.62/1.59  %Background operators:
% 3.62/1.59  
% 3.62/1.59  
% 3.62/1.59  %Foreground operators:
% 3.62/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.62/1.59  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.62/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.62/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.62/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.62/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.62/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.62/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.62/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.62/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.62/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.62/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.62/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.62/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.62/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.62/1.59  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 3.62/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.62/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.62/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.62/1.59  
% 3.62/1.60  tff(f_70, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ((r2_hidden(C, D) & r2_hidden(D, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_mcart_1)).
% 3.62/1.60  tff(f_34, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.62/1.60  tff(f_116, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 3.62/1.60  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.62/1.60  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.62/1.60  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.62/1.60  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 3.62/1.60  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.62/1.60  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.62/1.60  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.62/1.60  tff(f_103, axiom, (![A]: (?[B]: ((((((m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) & v1_relat_1(B)) & v4_relat_1(B, A)) & v5_relat_1(B, A)) & v1_funct_1(B)) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_funct_2)).
% 3.62/1.60  tff(c_22, plain, (![A_13]: (r2_hidden('#skF_1'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.62/1.60  tff(c_6, plain, (![A_2, B_3]: (v1_xboole_0(k2_zfmisc_1(A_2, B_3)) | ~v1_xboole_0(B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.62/1.60  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.62/1.60  tff(c_341, plain, (![C_56, B_57, A_58]: (~v1_xboole_0(C_56) | ~m1_subset_1(B_57, k1_zfmisc_1(C_56)) | ~r2_hidden(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.62/1.60  tff(c_357, plain, (![A_58]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_58, '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_341])).
% 3.62/1.60  tff(c_412, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_357])).
% 3.62/1.60  tff(c_416, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_6, c_412])).
% 3.62/1.60  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.62/1.60  tff(c_50, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.62/1.60  tff(c_58, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50])).
% 3.62/1.60  tff(c_52, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.62/1.60  tff(c_1003, plain, (![B_103, C_104, A_105]: (k1_xboole_0=B_103 | v1_funct_2(C_104, A_105, B_103) | k1_relset_1(A_105, B_103, C_104)!=A_105 | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_103))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.62/1.60  tff(c_1015, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_54, c_1003])).
% 3.62/1.60  tff(c_1026, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1015])).
% 3.62/1.60  tff(c_1027, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_58, c_1026])).
% 3.62/1.60  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.62/1.60  tff(c_1072, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1027, c_2])).
% 3.62/1.60  tff(c_1074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_416, c_1072])).
% 3.62/1.60  tff(c_1077, plain, (![A_106]: (~r2_hidden(A_106, '#skF_5'))), inference(splitRight, [status(thm)], [c_357])).
% 3.62/1.60  tff(c_1082, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22, c_1077])).
% 3.62/1.60  tff(c_99, plain, (![A_35]: (v1_xboole_0(k1_relat_1(A_35)) | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.62/1.60  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.62/1.60  tff(c_106, plain, (![A_38]: (k1_relat_1(A_38)=k1_xboole_0 | ~v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_99, c_4])).
% 3.62/1.60  tff(c_114, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_106])).
% 3.62/1.60  tff(c_1100, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1082, c_1082, c_114])).
% 3.62/1.60  tff(c_1190, plain, (![A_110, B_111, C_112]: (k1_relset_1(A_110, B_111, C_112)=k1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.62/1.60  tff(c_1202, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_1190])).
% 3.62/1.60  tff(c_1205, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1100, c_52, c_1202])).
% 3.62/1.60  tff(c_1218, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1205, c_52])).
% 3.62/1.60  tff(c_10, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.62/1.60  tff(c_24, plain, (![A_23]: (v1_funct_2(k1_xboole_0, A_23, k1_xboole_0) | k1_xboole_0=A_23 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_23, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.62/1.60  tff(c_62, plain, (![A_23]: (v1_funct_2(k1_xboole_0, A_23, k1_xboole_0) | k1_xboole_0=A_23 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_24])).
% 3.62/1.60  tff(c_397, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_62])).
% 3.62/1.60  tff(c_12, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.62/1.60  tff(c_143, plain, (![A_42]: (m1_subset_1('#skF_2'(A_42), k1_zfmisc_1(k2_zfmisc_1(A_42, A_42))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.62/1.60  tff(c_147, plain, (m1_subset_1('#skF_2'(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_143])).
% 3.62/1.60  tff(c_345, plain, (![A_58]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_58, '#skF_2'(k1_xboole_0)))), inference(resolution, [status(thm)], [c_147, c_341])).
% 3.62/1.60  tff(c_358, plain, (![A_59]: (~r2_hidden(A_59, '#skF_2'(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_345])).
% 3.62/1.60  tff(c_363, plain, ('#skF_2'(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_358])).
% 3.62/1.60  tff(c_365, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_147])).
% 3.62/1.60  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_397, c_365])).
% 3.62/1.60  tff(c_405, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_62])).
% 3.62/1.60  tff(c_1085, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1082, c_1082, c_405])).
% 3.62/1.60  tff(c_1346, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1205, c_1205, c_1085])).
% 3.62/1.60  tff(c_1215, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1205, c_1082])).
% 3.62/1.60  tff(c_28, plain, (![C_25, B_24]: (v1_funct_2(C_25, k1_xboole_0, B_24) | k1_relset_1(k1_xboole_0, B_24, C_25)!=k1_xboole_0 | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_24))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.62/1.60  tff(c_60, plain, (![C_25, B_24]: (v1_funct_2(C_25, k1_xboole_0, B_24) | k1_relset_1(k1_xboole_0, B_24, C_25)!=k1_xboole_0 | ~m1_subset_1(C_25, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_28])).
% 3.62/1.60  tff(c_1370, plain, (![C_122, B_123]: (v1_funct_2(C_122, '#skF_3', B_123) | k1_relset_1('#skF_3', B_123, C_122)!='#skF_3' | ~m1_subset_1(C_122, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_1215, c_1215, c_1215, c_60])).
% 3.62/1.60  tff(c_2144, plain, (![B_175]: (v1_funct_2('#skF_3', '#skF_3', B_175) | k1_relset_1('#skF_3', B_175, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_1346, c_1370])).
% 3.62/1.60  tff(c_1219, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1205, c_58])).
% 3.62/1.60  tff(c_2149, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_2144, c_1219])).
% 3.62/1.60  tff(c_2159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1218, c_2149])).
% 3.62/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.60  
% 3.62/1.60  Inference rules
% 3.62/1.60  ----------------------
% 3.62/1.60  #Ref     : 0
% 3.62/1.60  #Sup     : 480
% 3.62/1.60  #Fact    : 0
% 3.62/1.60  #Define  : 0
% 3.62/1.60  #Split   : 4
% 3.62/1.60  #Chain   : 0
% 3.62/1.60  #Close   : 0
% 3.62/1.60  
% 3.62/1.60  Ordering : KBO
% 3.62/1.60  
% 3.62/1.60  Simplification rules
% 3.62/1.60  ----------------------
% 3.62/1.60  #Subsume      : 91
% 3.62/1.60  #Demod        : 512
% 3.62/1.60  #Tautology    : 268
% 3.62/1.60  #SimpNegUnit  : 3
% 3.62/1.60  #BackRed      : 85
% 3.62/1.60  
% 3.62/1.60  #Partial instantiations: 0
% 3.62/1.60  #Strategies tried      : 1
% 3.62/1.60  
% 3.62/1.60  Timing (in seconds)
% 3.62/1.60  ----------------------
% 3.62/1.61  Preprocessing        : 0.31
% 3.62/1.61  Parsing              : 0.16
% 3.62/1.61  CNF conversion       : 0.02
% 3.62/1.61  Main loop            : 0.52
% 3.62/1.61  Inferencing          : 0.17
% 3.62/1.61  Reduction            : 0.18
% 3.62/1.61  Demodulation         : 0.13
% 3.62/1.61  BG Simplification    : 0.02
% 3.62/1.61  Subsumption          : 0.10
% 3.62/1.61  Abstraction          : 0.03
% 3.62/1.61  MUC search           : 0.00
% 3.62/1.61  Cooper               : 0.00
% 3.62/1.61  Total                : 0.87
% 3.62/1.61  Index Insertion      : 0.00
% 3.62/1.61  Index Deletion       : 0.00
% 3.62/1.61  Index Matching       : 0.00
% 3.62/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
