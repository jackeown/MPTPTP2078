%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:42 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 263 expanded)
%              Number of leaves         :   25 (  97 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 637 expanded)
%              Number of equality atoms :   55 ( 278 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( ~ ( A = k1_xboole_0
            & B != k1_xboole_0 )
        & ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ~ ( B = k1_relat_1(C)
                & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1391,plain,(
    ! [A_208] :
      ( r1_tarski(A_208,k2_zfmisc_1(k1_relat_1(A_208),k2_relat_1(A_208)))
      | ~ v1_relat_1(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,(
    ! [A_3] :
      ( r1_tarski(A_3,k2_zfmisc_1(k1_relat_1(A_3),k2_relat_1(A_3)))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_230,plain,(
    ! [A_55,B_56,C_57] :
      ( k1_relset_1(A_55,B_56,C_57) = k1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_330,plain,(
    ! [A_63,B_64,A_65] :
      ( k1_relset_1(A_63,B_64,A_65) = k1_relat_1(A_65)
      | ~ r1_tarski(A_65,k2_zfmisc_1(A_63,B_64)) ) ),
    inference(resolution,[status(thm)],[c_6,c_230])).

tff(c_347,plain,(
    ! [A_3] :
      ( k1_relset_1(k1_relat_1(A_3),k2_relat_1(A_3),A_3) = k1_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_330])).

tff(c_126,plain,(
    ! [A_35] :
      ( k2_relat_1(A_35) != k1_xboole_0
      | k1_xboole_0 = A_35
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_134,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_54,c_126])).

tff(c_153,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_528,plain,(
    ! [B_96,C_97,A_98] :
      ( k1_xboole_0 = B_96
      | v1_funct_2(C_97,A_98,B_96)
      | k1_relset_1(A_98,B_96,C_97) != A_98
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_679,plain,(
    ! [B_114,A_115,A_116] :
      ( k1_xboole_0 = B_114
      | v1_funct_2(A_115,A_116,B_114)
      | k1_relset_1(A_116,B_114,A_115) != A_116
      | ~ r1_tarski(A_115,k2_zfmisc_1(A_116,B_114)) ) ),
    inference(resolution,[status(thm)],[c_6,c_528])).

tff(c_740,plain,(
    ! [A_123] :
      ( k2_relat_1(A_123) = k1_xboole_0
      | v1_funct_2(A_123,k1_relat_1(A_123),k2_relat_1(A_123))
      | k1_relset_1(k1_relat_1(A_123),k2_relat_1(A_123),A_123) != k1_relat_1(A_123)
      | ~ v1_relat_1(A_123) ) ),
    inference(resolution,[status(thm)],[c_8,c_679])).

tff(c_52,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_56,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50])).

tff(c_69,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_747,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_740,c_69])).

tff(c_762,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_747])).

tff(c_763,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_762])).

tff(c_770,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_763])).

tff(c_774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_770])).

tff(c_775,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_18,plain,(
    ! [A_5] : k1_relat_1('#skF_1'(A_5,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    ! [A_5] : v1_relat_1('#skF_1'(A_5,k1_xboole_0)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_91,plain,(
    ! [A_33] :
      ( k1_relat_1(A_33) != k1_xboole_0
      | k1_xboole_0 = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_97,plain,(
    ! [A_5] :
      ( k1_relat_1('#skF_1'(A_5,k1_xboole_0)) != k1_xboole_0
      | '#skF_1'(A_5,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_91])).

tff(c_104,plain,(
    ! [A_5] : '#skF_1'(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_97])).

tff(c_107,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_18])).

tff(c_779,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_775,c_107])).

tff(c_105,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_54,c_91])).

tff(c_149,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_778,plain,(
    k1_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_149])).

tff(c_806,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_778])).

tff(c_807,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_809,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_807,c_107])).

tff(c_825,plain,(
    ~ v1_funct_2('#skF_2','#skF_2',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_809,c_69])).

tff(c_887,plain,(
    ! [A_136] :
      ( r1_tarski(A_136,k2_zfmisc_1(k1_relat_1(A_136),k2_relat_1(A_136)))
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_890,plain,
    ( r1_tarski('#skF_2',k2_zfmisc_1('#skF_2',k2_relat_1('#skF_2')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_887])).

tff(c_892,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_2',k2_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_890])).

tff(c_964,plain,(
    ! [A_150,B_151,C_152] :
      ( k1_relset_1(A_150,B_151,C_152) = k1_relat_1(C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1066,plain,(
    ! [A_159,B_160,A_161] :
      ( k1_relset_1(A_159,B_160,A_161) = k1_relat_1(A_161)
      | ~ r1_tarski(A_161,k2_zfmisc_1(A_159,B_160)) ) ),
    inference(resolution,[status(thm)],[c_6,c_964])).

tff(c_1069,plain,(
    k1_relset_1('#skF_2',k2_relat_1('#skF_2'),'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_892,c_1066])).

tff(c_1082,plain,(
    k1_relset_1('#skF_2',k2_relat_1('#skF_2'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_809,c_1069])).

tff(c_42,plain,(
    ! [C_20,B_19] :
      ( v1_funct_2(C_20,k1_xboole_0,B_19)
      | k1_relset_1(k1_xboole_0,B_19,C_20) != k1_xboole_0
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1132,plain,(
    ! [C_167,B_168] :
      ( v1_funct_2(C_167,'#skF_2',B_168)
      | k1_relset_1('#skF_2',B_168,C_167) != '#skF_2'
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_168))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_807,c_807,c_807,c_42])).

tff(c_1282,plain,(
    ! [A_194,B_195] :
      ( v1_funct_2(A_194,'#skF_2',B_195)
      | k1_relset_1('#skF_2',B_195,A_194) != '#skF_2'
      | ~ r1_tarski(A_194,k2_zfmisc_1('#skF_2',B_195)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1132])).

tff(c_1285,plain,
    ( v1_funct_2('#skF_2','#skF_2',k2_relat_1('#skF_2'))
    | k1_relset_1('#skF_2',k2_relat_1('#skF_2'),'#skF_2') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_892,c_1282])).

tff(c_1296,plain,(
    v1_funct_2('#skF_2','#skF_2',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1082,c_1285])).

tff(c_1298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_825,c_1296])).

tff(c_1299,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1390,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6,c_1299])).

tff(c_1394,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1391,c_1390])).

tff(c_1404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.51  
% 3.26/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.51  %$ v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.26/1.51  
% 3.26/1.51  %Foreground sorts:
% 3.26/1.51  
% 3.26/1.51  
% 3.26/1.51  %Background operators:
% 3.26/1.51  
% 3.26/1.51  
% 3.26/1.51  %Foreground operators:
% 3.26/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.26/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.26/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.26/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.51  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.26/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.26/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.26/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.26/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.26/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.26/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.26/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.51  
% 3.42/1.53  tff(f_109, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.42/1.53  tff(f_34, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 3.42/1.53  tff(f_30, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.42/1.53  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.42/1.53  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.42/1.53  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.42/1.53  tff(f_59, axiom, (![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 3.42/1.53  tff(c_54, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.42/1.53  tff(c_1391, plain, (![A_208]: (r1_tarski(A_208, k2_zfmisc_1(k1_relat_1(A_208), k2_relat_1(A_208))) | ~v1_relat_1(A_208))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.42/1.53  tff(c_6, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.42/1.53  tff(c_8, plain, (![A_3]: (r1_tarski(A_3, k2_zfmisc_1(k1_relat_1(A_3), k2_relat_1(A_3))) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.42/1.53  tff(c_230, plain, (![A_55, B_56, C_57]: (k1_relset_1(A_55, B_56, C_57)=k1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.42/1.53  tff(c_330, plain, (![A_63, B_64, A_65]: (k1_relset_1(A_63, B_64, A_65)=k1_relat_1(A_65) | ~r1_tarski(A_65, k2_zfmisc_1(A_63, B_64)))), inference(resolution, [status(thm)], [c_6, c_230])).
% 3.42/1.53  tff(c_347, plain, (![A_3]: (k1_relset_1(k1_relat_1(A_3), k2_relat_1(A_3), A_3)=k1_relat_1(A_3) | ~v1_relat_1(A_3))), inference(resolution, [status(thm)], [c_8, c_330])).
% 3.42/1.53  tff(c_126, plain, (![A_35]: (k2_relat_1(A_35)!=k1_xboole_0 | k1_xboole_0=A_35 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.42/1.53  tff(c_134, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_54, c_126])).
% 3.42/1.53  tff(c_153, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_134])).
% 3.42/1.53  tff(c_528, plain, (![B_96, C_97, A_98]: (k1_xboole_0=B_96 | v1_funct_2(C_97, A_98, B_96) | k1_relset_1(A_98, B_96, C_97)!=A_98 | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_96))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.42/1.53  tff(c_679, plain, (![B_114, A_115, A_116]: (k1_xboole_0=B_114 | v1_funct_2(A_115, A_116, B_114) | k1_relset_1(A_116, B_114, A_115)!=A_116 | ~r1_tarski(A_115, k2_zfmisc_1(A_116, B_114)))), inference(resolution, [status(thm)], [c_6, c_528])).
% 3.42/1.53  tff(c_740, plain, (![A_123]: (k2_relat_1(A_123)=k1_xboole_0 | v1_funct_2(A_123, k1_relat_1(A_123), k2_relat_1(A_123)) | k1_relset_1(k1_relat_1(A_123), k2_relat_1(A_123), A_123)!=k1_relat_1(A_123) | ~v1_relat_1(A_123))), inference(resolution, [status(thm)], [c_8, c_679])).
% 3.42/1.53  tff(c_52, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.42/1.53  tff(c_50, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.42/1.53  tff(c_56, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50])).
% 3.42/1.53  tff(c_69, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_56])).
% 3.42/1.53  tff(c_747, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_740, c_69])).
% 3.42/1.53  tff(c_762, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_747])).
% 3.42/1.53  tff(c_763, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_153, c_762])).
% 3.42/1.53  tff(c_770, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_347, c_763])).
% 3.42/1.53  tff(c_774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_770])).
% 3.42/1.53  tff(c_775, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_134])).
% 3.42/1.53  tff(c_18, plain, (![A_5]: (k1_relat_1('#skF_1'(A_5, k1_xboole_0))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.42/1.53  tff(c_26, plain, (![A_5]: (v1_relat_1('#skF_1'(A_5, k1_xboole_0)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.42/1.53  tff(c_91, plain, (![A_33]: (k1_relat_1(A_33)!=k1_xboole_0 | k1_xboole_0=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.42/1.53  tff(c_97, plain, (![A_5]: (k1_relat_1('#skF_1'(A_5, k1_xboole_0))!=k1_xboole_0 | '#skF_1'(A_5, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_91])).
% 3.42/1.53  tff(c_104, plain, (![A_5]: ('#skF_1'(A_5, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_97])).
% 3.42/1.53  tff(c_107, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_104, c_18])).
% 3.42/1.53  tff(c_779, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_775, c_775, c_107])).
% 3.42/1.53  tff(c_105, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_54, c_91])).
% 3.42/1.53  tff(c_149, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_105])).
% 3.42/1.53  tff(c_778, plain, (k1_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_775, c_149])).
% 3.42/1.53  tff(c_806, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_779, c_778])).
% 3.42/1.53  tff(c_807, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_105])).
% 3.42/1.53  tff(c_809, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_807, c_807, c_107])).
% 3.42/1.53  tff(c_825, plain, (~v1_funct_2('#skF_2', '#skF_2', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_809, c_69])).
% 3.42/1.53  tff(c_887, plain, (![A_136]: (r1_tarski(A_136, k2_zfmisc_1(k1_relat_1(A_136), k2_relat_1(A_136))) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.42/1.53  tff(c_890, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_2', k2_relat_1('#skF_2'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_809, c_887])).
% 3.42/1.53  tff(c_892, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_2', k2_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_890])).
% 3.42/1.53  tff(c_964, plain, (![A_150, B_151, C_152]: (k1_relset_1(A_150, B_151, C_152)=k1_relat_1(C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.42/1.53  tff(c_1066, plain, (![A_159, B_160, A_161]: (k1_relset_1(A_159, B_160, A_161)=k1_relat_1(A_161) | ~r1_tarski(A_161, k2_zfmisc_1(A_159, B_160)))), inference(resolution, [status(thm)], [c_6, c_964])).
% 3.42/1.53  tff(c_1069, plain, (k1_relset_1('#skF_2', k2_relat_1('#skF_2'), '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_892, c_1066])).
% 3.42/1.53  tff(c_1082, plain, (k1_relset_1('#skF_2', k2_relat_1('#skF_2'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_809, c_1069])).
% 3.42/1.53  tff(c_42, plain, (![C_20, B_19]: (v1_funct_2(C_20, k1_xboole_0, B_19) | k1_relset_1(k1_xboole_0, B_19, C_20)!=k1_xboole_0 | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_19))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.42/1.53  tff(c_1132, plain, (![C_167, B_168]: (v1_funct_2(C_167, '#skF_2', B_168) | k1_relset_1('#skF_2', B_168, C_167)!='#skF_2' | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_168))))), inference(demodulation, [status(thm), theory('equality')], [c_807, c_807, c_807, c_807, c_42])).
% 3.42/1.53  tff(c_1282, plain, (![A_194, B_195]: (v1_funct_2(A_194, '#skF_2', B_195) | k1_relset_1('#skF_2', B_195, A_194)!='#skF_2' | ~r1_tarski(A_194, k2_zfmisc_1('#skF_2', B_195)))), inference(resolution, [status(thm)], [c_6, c_1132])).
% 3.42/1.53  tff(c_1285, plain, (v1_funct_2('#skF_2', '#skF_2', k2_relat_1('#skF_2')) | k1_relset_1('#skF_2', k2_relat_1('#skF_2'), '#skF_2')!='#skF_2'), inference(resolution, [status(thm)], [c_892, c_1282])).
% 3.42/1.53  tff(c_1296, plain, (v1_funct_2('#skF_2', '#skF_2', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1082, c_1285])).
% 3.42/1.53  tff(c_1298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_825, c_1296])).
% 3.42/1.53  tff(c_1299, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_56])).
% 3.42/1.53  tff(c_1390, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_6, c_1299])).
% 3.42/1.53  tff(c_1394, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1391, c_1390])).
% 3.42/1.53  tff(c_1404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1394])).
% 3.42/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.53  
% 3.42/1.53  Inference rules
% 3.42/1.53  ----------------------
% 3.42/1.53  #Ref     : 0
% 3.42/1.53  #Sup     : 261
% 3.42/1.53  #Fact    : 0
% 3.42/1.53  #Define  : 0
% 3.42/1.53  #Split   : 8
% 3.42/1.53  #Chain   : 0
% 3.42/1.53  #Close   : 0
% 3.42/1.53  
% 3.42/1.53  Ordering : KBO
% 3.42/1.53  
% 3.42/1.53  Simplification rules
% 3.42/1.53  ----------------------
% 3.42/1.53  #Subsume      : 18
% 3.42/1.53  #Demod        : 302
% 3.42/1.53  #Tautology    : 164
% 3.42/1.53  #SimpNegUnit  : 2
% 3.42/1.53  #BackRed      : 45
% 3.42/1.53  
% 3.42/1.53  #Partial instantiations: 0
% 3.42/1.53  #Strategies tried      : 1
% 3.42/1.53  
% 3.42/1.53  Timing (in seconds)
% 3.42/1.53  ----------------------
% 3.42/1.53  Preprocessing        : 0.32
% 3.42/1.53  Parsing              : 0.17
% 3.42/1.53  CNF conversion       : 0.02
% 3.42/1.53  Main loop            : 0.44
% 3.42/1.53  Inferencing          : 0.17
% 3.42/1.53  Reduction            : 0.13
% 3.42/1.53  Demodulation         : 0.09
% 3.42/1.53  BG Simplification    : 0.02
% 3.42/1.53  Subsumption          : 0.08
% 3.42/1.53  Abstraction          : 0.03
% 3.42/1.53  MUC search           : 0.00
% 3.42/1.53  Cooper               : 0.00
% 3.42/1.53  Total                : 0.80
% 3.42/1.53  Index Insertion      : 0.00
% 3.42/1.53  Index Deletion       : 0.00
% 3.42/1.53  Index Matching       : 0.00
% 3.42/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
