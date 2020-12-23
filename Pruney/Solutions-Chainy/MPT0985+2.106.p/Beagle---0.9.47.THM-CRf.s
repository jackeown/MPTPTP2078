%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:43 EST 2020

% Result     : Theorem 9.84s
% Output     : CNFRefutation 9.84s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 697 expanded)
%              Number of leaves         :   38 ( 231 expanded)
%              Depth                    :   13
%              Number of atoms          :  301 (1977 expanded)
%              Number of equality atoms :   78 ( 350 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_123,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_95,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_226,plain,(
    ! [C_55,B_56,A_57] :
      ( v1_xboole_0(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(B_56,A_57)))
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_244,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_226])).

tff(c_249,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_22,plain,(
    ! [A_11] :
      ( v1_funct_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_142,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_145,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_142])).

tff(c_148,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_145])).

tff(c_149,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_155,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_149])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_155])).

tff(c_169,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_201,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_171,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_187,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_171])).

tff(c_62,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_421,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_440,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_421])).

tff(c_666,plain,(
    ! [B_99,A_100,C_101] :
      ( k1_xboole_0 = B_99
      | k1_relset_1(A_100,B_99,C_101) = A_100
      | ~ v1_funct_2(C_101,A_100,B_99)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_678,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_666])).

tff(c_697,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_440,c_678])).

tff(c_701,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_697])).

tff(c_26,plain,(
    ! [A_12] :
      ( k2_relat_1(k2_funct_1(A_12)) = k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_170,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_401,plain,(
    ! [A_71] :
      ( k2_relat_1(k2_funct_1(A_71)) = k1_relat_1(A_71)
      | ~ v2_funct_1(A_71)
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_54,plain,(
    ! [A_30] :
      ( v1_funct_2(A_30,k1_relat_1(A_30),k2_relat_1(A_30))
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_5009,plain,(
    ! [A_172] :
      ( v1_funct_2(k2_funct_1(A_172),k1_relat_1(k2_funct_1(A_172)),k1_relat_1(A_172))
      | ~ v1_funct_1(k2_funct_1(A_172))
      | ~ v1_relat_1(k2_funct_1(A_172))
      | ~ v2_funct_1(A_172)
      | ~ v1_funct_1(A_172)
      | ~ v1_relat_1(A_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_54])).

tff(c_5012,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_701,c_5009])).

tff(c_5026,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_68,c_62,c_170,c_5012])).

tff(c_5031,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5026])).

tff(c_5034,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_5031])).

tff(c_5038,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_68,c_5034])).

tff(c_5040,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5026])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_485,plain,(
    ! [A_84,B_85,C_86] :
      ( k2_relset_1(A_84,B_85,C_86) = k2_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_491,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_485])).

tff(c_505,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_491])).

tff(c_28,plain,(
    ! [A_12] :
      ( k1_relat_1(k2_funct_1(A_12)) = k2_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_524,plain,(
    ! [A_89] :
      ( m1_subset_1(A_89,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_89),k2_relat_1(A_89))))
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6998,plain,(
    ! [A_189] :
      ( m1_subset_1(k2_funct_1(A_189),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_189),k2_relat_1(k2_funct_1(A_189)))))
      | ~ v1_funct_1(k2_funct_1(A_189))
      | ~ v1_relat_1(k2_funct_1(A_189))
      | ~ v2_funct_1(A_189)
      | ~ v1_funct_1(A_189)
      | ~ v1_relat_1(A_189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_524])).

tff(c_7021,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_6998])).

tff(c_7042,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_68,c_62,c_5040,c_170,c_7021])).

tff(c_7069,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_7042])).

tff(c_7082,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_68,c_62,c_701,c_7069])).

tff(c_7084,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_7082])).

tff(c_7085,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_697])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_7109,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7085,c_2])).

tff(c_7111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_7109])).

tff(c_7112,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_7120,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_7112,c_4])).

tff(c_12,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_7133,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7120,c_7120,c_12])).

tff(c_7113,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_7127,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_7113,c_4])).

tff(c_7144,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7120,c_7127])).

tff(c_7146,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7144,c_201])).

tff(c_7340,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7133,c_7146])).

tff(c_38,plain,(
    ! [A_26] : m1_subset_1(k6_relat_1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_7228,plain,(
    ! [A_197] :
      ( v1_xboole_0(k6_relat_1(A_197))
      | ~ v1_xboole_0(A_197) ) ),
    inference(resolution,[status(thm)],[c_38,c_226])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( ~ v1_xboole_0(B_3)
      | B_3 = A_2
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7119,plain,(
    ! [A_2] :
      ( A_2 = '#skF_3'
      | ~ v1_xboole_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_7112,c_6])).

tff(c_7253,plain,(
    ! [A_199] :
      ( k6_relat_1(A_199) = '#skF_3'
      | ~ v1_xboole_0(A_199) ) ),
    inference(resolution,[status(thm)],[c_7228,c_7119])).

tff(c_7261,plain,(
    k6_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_7112,c_7253])).

tff(c_18,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_7278,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7261,c_18])).

tff(c_7320,plain,(
    ! [A_201] :
      ( k2_relat_1(k2_funct_1(A_201)) = k1_relat_1(A_201)
      | ~ v2_funct_1(A_201)
      | ~ v1_funct_1(A_201)
      | ~ v1_relat_1(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12286,plain,(
    ! [A_300] :
      ( v1_funct_2(k2_funct_1(A_300),k1_relat_1(k2_funct_1(A_300)),k1_relat_1(A_300))
      | ~ v1_funct_1(k2_funct_1(A_300))
      | ~ v1_relat_1(k2_funct_1(A_300))
      | ~ v2_funct_1(A_300)
      | ~ v1_funct_1(A_300)
      | ~ v1_relat_1(A_300) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7320,c_54])).

tff(c_12289,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7278,c_12286])).

tff(c_12300,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_68,c_62,c_170,c_12289])).

tff(c_12303,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_12300])).

tff(c_12306,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_12303])).

tff(c_12310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_68,c_12306])).

tff(c_12312,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_12300])).

tff(c_20,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_7281,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7261,c_20])).

tff(c_8006,plain,(
    ! [A_250] :
      ( m1_subset_1(A_250,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_250),k2_relat_1(A_250))))
      | ~ v1_funct_1(A_250)
      | ~ v1_relat_1(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_13530,plain,(
    ! [A_308] :
      ( m1_subset_1(k2_funct_1(A_308),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_308),k2_relat_1(k2_funct_1(A_308)))))
      | ~ v1_funct_1(k2_funct_1(A_308))
      | ~ v1_relat_1(k2_funct_1(A_308))
      | ~ v2_funct_1(A_308)
      | ~ v1_funct_1(A_308)
      | ~ v1_relat_1(A_308) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8006])).

tff(c_13559,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7281,c_13530])).

tff(c_13571,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_68,c_62,c_12312,c_170,c_7133,c_13559])).

tff(c_13573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7340,c_13571])).

tff(c_13575,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_13592,plain,(
    ! [C_310,B_311,A_312] :
      ( v1_xboole_0(C_310)
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(B_311,A_312)))
      | ~ v1_xboole_0(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_13612,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_13575,c_13592])).

tff(c_13620,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_13612])).

tff(c_14167,plain,(
    ! [A_347,B_348,C_349] :
      ( k2_relset_1(A_347,B_348,C_349) = k2_relat_1(C_349)
      | ~ m1_subset_1(C_349,k1_zfmisc_1(k2_zfmisc_1(A_347,B_348))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14176,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_14167])).

tff(c_14191,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_14176])).

tff(c_13574,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_14241,plain,(
    ! [A_353,B_354,C_355] :
      ( k1_relset_1(A_353,B_354,C_355) = k1_relat_1(C_355)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_14261,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_13575,c_14241])).

tff(c_15221,plain,(
    ! [B_390,C_391,A_392] :
      ( k1_xboole_0 = B_390
      | v1_funct_2(C_391,A_392,B_390)
      | k1_relset_1(A_392,B_390,C_391) != A_392
      | ~ m1_subset_1(C_391,k1_zfmisc_1(k2_zfmisc_1(A_392,B_390))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_15227,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_13575,c_15221])).

tff(c_15246,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14261,c_15227])).

tff(c_15247,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_13574,c_15246])).

tff(c_15257,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_15247])).

tff(c_15260,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_15257])).

tff(c_15263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_68,c_62,c_14191,c_15260])).

tff(c_15264,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_15247])).

tff(c_15297,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15264,c_2])).

tff(c_15299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13620,c_15297])).

tff(c_15301,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_13612])).

tff(c_15308,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_15301,c_4])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_188,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_171])).

tff(c_15310,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15308,c_188])).

tff(c_15300,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_13612])).

tff(c_15337,plain,(
    ! [A_396] :
      ( A_396 = '#skF_1'
      | ~ v1_xboole_0(A_396) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15308,c_4])).

tff(c_15344,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_15300,c_15337])).

tff(c_15352,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15344,c_170])).

tff(c_15445,plain,(
    ! [A_403] :
      ( v1_xboole_0(k6_relat_1(A_403))
      | ~ v1_xboole_0(A_403) ) ),
    inference(resolution,[status(thm)],[c_38,c_13592])).

tff(c_15317,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15308,c_4])).

tff(c_15485,plain,(
    ! [A_405] :
      ( k6_relat_1(A_405) = '#skF_1'
      | ~ v1_xboole_0(A_405) ) ),
    inference(resolution,[status(thm)],[c_15445,c_15317])).

tff(c_15493,plain,(
    k6_relat_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_15301,c_15485])).

tff(c_15507,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_15493,c_18])).

tff(c_15510,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_15493,c_20])).

tff(c_15531,plain,
    ( v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15510,c_54])).

tff(c_15535,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15310,c_15352,c_15507,c_15531])).

tff(c_40,plain,(
    ! [A_27] :
      ( v1_funct_2(k1_xboole_0,A_27,k1_xboole_0)
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_27,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_70,plain,(
    ! [A_27] :
      ( v1_funct_2(k1_xboole_0,A_27,k1_xboole_0)
      | k1_xboole_0 = A_27 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_15659,plain,(
    ! [A_410] :
      ( v1_funct_2('#skF_1',A_410,'#skF_1')
      | A_410 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15308,c_15308,c_15308,c_70])).

tff(c_15351,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15344,c_13574])).

tff(c_15669,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_15659,c_15351])).

tff(c_15672,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15669,c_15351])).

tff(c_15677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15535,c_15672])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:35:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.84/3.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.84/3.22  
% 9.84/3.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.84/3.22  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 9.84/3.22  
% 9.84/3.22  %Foreground sorts:
% 9.84/3.22  
% 9.84/3.22  
% 9.84/3.22  %Background operators:
% 9.84/3.22  
% 9.84/3.22  
% 9.84/3.22  %Foreground operators:
% 9.84/3.22  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.84/3.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.84/3.22  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.84/3.22  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.84/3.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.84/3.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.84/3.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.84/3.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.84/3.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.84/3.22  tff('#skF_2', type, '#skF_2': $i).
% 9.84/3.22  tff('#skF_3', type, '#skF_3': $i).
% 9.84/3.22  tff('#skF_1', type, '#skF_1': $i).
% 9.84/3.22  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.84/3.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.84/3.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.84/3.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.84/3.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.84/3.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.84/3.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.84/3.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.84/3.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.84/3.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.84/3.22  
% 9.84/3.25  tff(f_140, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 9.84/3.25  tff(f_85, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 9.84/3.25  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.84/3.25  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.84/3.25  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.84/3.25  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.84/3.25  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 9.84/3.25  tff(f_123, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 9.84/3.25  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.84/3.25  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.84/3.25  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.84/3.25  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.84/3.25  tff(f_95, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 9.84/3.25  tff(f_38, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 9.84/3.25  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 9.84/3.25  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 9.84/3.25  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.84/3.25  tff(c_226, plain, (![C_55, B_56, A_57]: (v1_xboole_0(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(B_56, A_57))) | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.84/3.25  tff(c_244, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_226])).
% 9.84/3.25  tff(c_249, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_244])).
% 9.84/3.25  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.84/3.25  tff(c_22, plain, (![A_11]: (v1_funct_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.84/3.25  tff(c_58, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.84/3.25  tff(c_142, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_58])).
% 9.84/3.25  tff(c_145, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_142])).
% 9.84/3.25  tff(c_148, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_145])).
% 9.84/3.25  tff(c_149, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.84/3.25  tff(c_155, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_149])).
% 9.84/3.25  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_155])).
% 9.84/3.25  tff(c_169, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_58])).
% 9.84/3.25  tff(c_201, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_169])).
% 9.84/3.25  tff(c_171, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.84/3.25  tff(c_187, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_171])).
% 9.84/3.25  tff(c_62, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.84/3.25  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.84/3.25  tff(c_421, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.84/3.25  tff(c_440, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_421])).
% 9.84/3.25  tff(c_666, plain, (![B_99, A_100, C_101]: (k1_xboole_0=B_99 | k1_relset_1(A_100, B_99, C_101)=A_100 | ~v1_funct_2(C_101, A_100, B_99) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.84/3.25  tff(c_678, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_666])).
% 9.84/3.25  tff(c_697, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_440, c_678])).
% 9.84/3.25  tff(c_701, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_697])).
% 9.84/3.25  tff(c_26, plain, (![A_12]: (k2_relat_1(k2_funct_1(A_12))=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.84/3.25  tff(c_24, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.84/3.25  tff(c_170, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_58])).
% 9.84/3.25  tff(c_401, plain, (![A_71]: (k2_relat_1(k2_funct_1(A_71))=k1_relat_1(A_71) | ~v2_funct_1(A_71) | ~v1_funct_1(A_71) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.84/3.25  tff(c_54, plain, (![A_30]: (v1_funct_2(A_30, k1_relat_1(A_30), k2_relat_1(A_30)) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.84/3.25  tff(c_5009, plain, (![A_172]: (v1_funct_2(k2_funct_1(A_172), k1_relat_1(k2_funct_1(A_172)), k1_relat_1(A_172)) | ~v1_funct_1(k2_funct_1(A_172)) | ~v1_relat_1(k2_funct_1(A_172)) | ~v2_funct_1(A_172) | ~v1_funct_1(A_172) | ~v1_relat_1(A_172))), inference(superposition, [status(thm), theory('equality')], [c_401, c_54])).
% 9.84/3.25  tff(c_5012, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_701, c_5009])).
% 9.84/3.25  tff(c_5026, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_68, c_62, c_170, c_5012])).
% 9.84/3.25  tff(c_5031, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5026])).
% 9.84/3.25  tff(c_5034, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_5031])).
% 9.84/3.25  tff(c_5038, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_187, c_68, c_5034])).
% 9.84/3.25  tff(c_5040, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5026])).
% 9.84/3.25  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.84/3.25  tff(c_485, plain, (![A_84, B_85, C_86]: (k2_relset_1(A_84, B_85, C_86)=k2_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.84/3.25  tff(c_491, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_485])).
% 9.84/3.25  tff(c_505, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_491])).
% 9.84/3.25  tff(c_28, plain, (![A_12]: (k1_relat_1(k2_funct_1(A_12))=k2_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.84/3.25  tff(c_524, plain, (![A_89]: (m1_subset_1(A_89, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_89), k2_relat_1(A_89)))) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.84/3.25  tff(c_6998, plain, (![A_189]: (m1_subset_1(k2_funct_1(A_189), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_189), k2_relat_1(k2_funct_1(A_189))))) | ~v1_funct_1(k2_funct_1(A_189)) | ~v1_relat_1(k2_funct_1(A_189)) | ~v2_funct_1(A_189) | ~v1_funct_1(A_189) | ~v1_relat_1(A_189))), inference(superposition, [status(thm), theory('equality')], [c_28, c_524])).
% 9.84/3.25  tff(c_7021, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_505, c_6998])).
% 9.84/3.25  tff(c_7042, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_68, c_62, c_5040, c_170, c_7021])).
% 9.84/3.25  tff(c_7069, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_7042])).
% 9.84/3.25  tff(c_7082, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_68, c_62, c_701, c_7069])).
% 9.84/3.25  tff(c_7084, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_7082])).
% 9.84/3.25  tff(c_7085, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_697])).
% 9.84/3.25  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.84/3.25  tff(c_7109, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7085, c_2])).
% 9.84/3.25  tff(c_7111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_7109])).
% 9.84/3.25  tff(c_7112, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_244])).
% 9.84/3.25  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 9.84/3.25  tff(c_7120, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_7112, c_4])).
% 9.84/3.25  tff(c_12, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.84/3.25  tff(c_7133, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7120, c_7120, c_12])).
% 9.84/3.25  tff(c_7113, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_244])).
% 9.84/3.25  tff(c_7127, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_7113, c_4])).
% 9.84/3.25  tff(c_7144, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7120, c_7127])).
% 9.84/3.25  tff(c_7146, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_7144, c_201])).
% 9.84/3.25  tff(c_7340, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7133, c_7146])).
% 9.84/3.25  tff(c_38, plain, (![A_26]: (m1_subset_1(k6_relat_1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.84/3.25  tff(c_7228, plain, (![A_197]: (v1_xboole_0(k6_relat_1(A_197)) | ~v1_xboole_0(A_197))), inference(resolution, [status(thm)], [c_38, c_226])).
% 9.84/3.25  tff(c_6, plain, (![B_3, A_2]: (~v1_xboole_0(B_3) | B_3=A_2 | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.84/3.25  tff(c_7119, plain, (![A_2]: (A_2='#skF_3' | ~v1_xboole_0(A_2))), inference(resolution, [status(thm)], [c_7112, c_6])).
% 9.84/3.25  tff(c_7253, plain, (![A_199]: (k6_relat_1(A_199)='#skF_3' | ~v1_xboole_0(A_199))), inference(resolution, [status(thm)], [c_7228, c_7119])).
% 9.84/3.25  tff(c_7261, plain, (k6_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_7112, c_7253])).
% 9.84/3.25  tff(c_18, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.84/3.25  tff(c_7278, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_7261, c_18])).
% 9.84/3.25  tff(c_7320, plain, (![A_201]: (k2_relat_1(k2_funct_1(A_201))=k1_relat_1(A_201) | ~v2_funct_1(A_201) | ~v1_funct_1(A_201) | ~v1_relat_1(A_201))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.84/3.25  tff(c_12286, plain, (![A_300]: (v1_funct_2(k2_funct_1(A_300), k1_relat_1(k2_funct_1(A_300)), k1_relat_1(A_300)) | ~v1_funct_1(k2_funct_1(A_300)) | ~v1_relat_1(k2_funct_1(A_300)) | ~v2_funct_1(A_300) | ~v1_funct_1(A_300) | ~v1_relat_1(A_300))), inference(superposition, [status(thm), theory('equality')], [c_7320, c_54])).
% 9.84/3.25  tff(c_12289, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7278, c_12286])).
% 9.84/3.25  tff(c_12300, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_68, c_62, c_170, c_12289])).
% 9.84/3.25  tff(c_12303, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_12300])).
% 9.84/3.25  tff(c_12306, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_12303])).
% 9.84/3.25  tff(c_12310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_187, c_68, c_12306])).
% 9.84/3.25  tff(c_12312, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_12300])).
% 9.84/3.25  tff(c_20, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.84/3.25  tff(c_7281, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_7261, c_20])).
% 9.84/3.25  tff(c_8006, plain, (![A_250]: (m1_subset_1(A_250, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_250), k2_relat_1(A_250)))) | ~v1_funct_1(A_250) | ~v1_relat_1(A_250))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.84/3.25  tff(c_13530, plain, (![A_308]: (m1_subset_1(k2_funct_1(A_308), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_308), k2_relat_1(k2_funct_1(A_308))))) | ~v1_funct_1(k2_funct_1(A_308)) | ~v1_relat_1(k2_funct_1(A_308)) | ~v2_funct_1(A_308) | ~v1_funct_1(A_308) | ~v1_relat_1(A_308))), inference(superposition, [status(thm), theory('equality')], [c_28, c_8006])).
% 9.84/3.25  tff(c_13559, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7281, c_13530])).
% 9.84/3.25  tff(c_13571, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_68, c_62, c_12312, c_170, c_7133, c_13559])).
% 9.84/3.25  tff(c_13573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7340, c_13571])).
% 9.84/3.25  tff(c_13575, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_169])).
% 9.84/3.25  tff(c_13592, plain, (![C_310, B_311, A_312]: (v1_xboole_0(C_310) | ~m1_subset_1(C_310, k1_zfmisc_1(k2_zfmisc_1(B_311, A_312))) | ~v1_xboole_0(A_312))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.84/3.25  tff(c_13612, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_13575, c_13592])).
% 9.84/3.25  tff(c_13620, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_13612])).
% 9.84/3.25  tff(c_14167, plain, (![A_347, B_348, C_349]: (k2_relset_1(A_347, B_348, C_349)=k2_relat_1(C_349) | ~m1_subset_1(C_349, k1_zfmisc_1(k2_zfmisc_1(A_347, B_348))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.84/3.25  tff(c_14176, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_14167])).
% 9.84/3.25  tff(c_14191, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_14176])).
% 9.84/3.25  tff(c_13574, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_169])).
% 9.84/3.25  tff(c_14241, plain, (![A_353, B_354, C_355]: (k1_relset_1(A_353, B_354, C_355)=k1_relat_1(C_355) | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.84/3.25  tff(c_14261, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_13575, c_14241])).
% 9.84/3.25  tff(c_15221, plain, (![B_390, C_391, A_392]: (k1_xboole_0=B_390 | v1_funct_2(C_391, A_392, B_390) | k1_relset_1(A_392, B_390, C_391)!=A_392 | ~m1_subset_1(C_391, k1_zfmisc_1(k2_zfmisc_1(A_392, B_390))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.84/3.25  tff(c_15227, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_13575, c_15221])).
% 9.84/3.25  tff(c_15246, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14261, c_15227])).
% 9.84/3.25  tff(c_15247, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_13574, c_15246])).
% 9.84/3.25  tff(c_15257, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_15247])).
% 9.84/3.25  tff(c_15260, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_15257])).
% 9.84/3.25  tff(c_15263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_187, c_68, c_62, c_14191, c_15260])).
% 9.84/3.25  tff(c_15264, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_15247])).
% 9.84/3.25  tff(c_15297, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15264, c_2])).
% 9.84/3.25  tff(c_15299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13620, c_15297])).
% 9.84/3.25  tff(c_15301, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_13612])).
% 9.84/3.25  tff(c_15308, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_15301, c_4])).
% 9.84/3.25  tff(c_14, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.84/3.25  tff(c_188, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_171])).
% 9.84/3.25  tff(c_15310, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15308, c_188])).
% 9.84/3.25  tff(c_15300, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_13612])).
% 9.84/3.25  tff(c_15337, plain, (![A_396]: (A_396='#skF_1' | ~v1_xboole_0(A_396))), inference(demodulation, [status(thm), theory('equality')], [c_15308, c_4])).
% 9.84/3.25  tff(c_15344, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_15300, c_15337])).
% 9.84/3.25  tff(c_15352, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15344, c_170])).
% 9.84/3.25  tff(c_15445, plain, (![A_403]: (v1_xboole_0(k6_relat_1(A_403)) | ~v1_xboole_0(A_403))), inference(resolution, [status(thm)], [c_38, c_13592])).
% 9.84/3.25  tff(c_15317, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_15308, c_4])).
% 9.84/3.25  tff(c_15485, plain, (![A_405]: (k6_relat_1(A_405)='#skF_1' | ~v1_xboole_0(A_405))), inference(resolution, [status(thm)], [c_15445, c_15317])).
% 9.84/3.25  tff(c_15493, plain, (k6_relat_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_15301, c_15485])).
% 9.84/3.25  tff(c_15507, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_15493, c_18])).
% 9.84/3.25  tff(c_15510, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_15493, c_20])).
% 9.84/3.25  tff(c_15531, plain, (v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15510, c_54])).
% 9.84/3.25  tff(c_15535, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15310, c_15352, c_15507, c_15531])).
% 9.84/3.25  tff(c_40, plain, (![A_27]: (v1_funct_2(k1_xboole_0, A_27, k1_xboole_0) | k1_xboole_0=A_27 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_27, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.84/3.25  tff(c_70, plain, (![A_27]: (v1_funct_2(k1_xboole_0, A_27, k1_xboole_0) | k1_xboole_0=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40])).
% 9.84/3.25  tff(c_15659, plain, (![A_410]: (v1_funct_2('#skF_1', A_410, '#skF_1') | A_410='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15308, c_15308, c_15308, c_70])).
% 9.84/3.25  tff(c_15351, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15344, c_13574])).
% 9.84/3.25  tff(c_15669, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_15659, c_15351])).
% 9.84/3.25  tff(c_15672, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15669, c_15351])).
% 9.84/3.25  tff(c_15677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15535, c_15672])).
% 9.84/3.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.84/3.25  
% 9.84/3.25  Inference rules
% 9.84/3.25  ----------------------
% 9.84/3.25  #Ref     : 0
% 9.84/3.25  #Sup     : 4442
% 9.84/3.25  #Fact    : 0
% 9.84/3.25  #Define  : 0
% 9.84/3.25  #Split   : 21
% 9.84/3.25  #Chain   : 0
% 9.84/3.25  #Close   : 0
% 9.84/3.25  
% 9.84/3.25  Ordering : KBO
% 9.84/3.25  
% 9.84/3.25  Simplification rules
% 9.84/3.25  ----------------------
% 9.84/3.25  #Subsume      : 1849
% 9.84/3.25  #Demod        : 2639
% 9.84/3.25  #Tautology    : 878
% 9.84/3.25  #SimpNegUnit  : 6
% 9.84/3.25  #BackRed      : 120
% 9.84/3.25  
% 9.84/3.25  #Partial instantiations: 0
% 9.84/3.25  #Strategies tried      : 1
% 9.84/3.25  
% 9.84/3.25  Timing (in seconds)
% 9.84/3.25  ----------------------
% 9.84/3.25  Preprocessing        : 0.37
% 9.84/3.25  Parsing              : 0.19
% 9.84/3.25  CNF conversion       : 0.02
% 9.84/3.25  Main loop            : 2.02
% 9.84/3.25  Inferencing          : 0.54
% 9.84/3.25  Reduction            : 0.66
% 9.84/3.25  Demodulation         : 0.50
% 9.84/3.25  BG Simplification    : 0.08
% 9.84/3.25  Subsumption          : 0.62
% 9.84/3.25  Abstraction          : 0.10
% 9.84/3.25  MUC search           : 0.00
% 9.84/3.25  Cooper               : 0.00
% 9.84/3.25  Total                : 2.45
% 9.84/3.25  Index Insertion      : 0.00
% 9.84/3.25  Index Deletion       : 0.00
% 9.84/3.25  Index Matching       : 0.00
% 9.84/3.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
