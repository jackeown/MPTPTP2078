%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:44 EST 2020

% Result     : Theorem 4.46s
% Output     : CNFRefutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 729 expanded)
%              Number of leaves         :   38 ( 249 expanded)
%              Depth                    :   12
%              Number of atoms          :  308 (2077 expanded)
%              Number of equality atoms :  119 ( 601 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_110,axiom,(
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

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_46,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_259,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_271,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_259])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_72,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_70,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1766,plain,(
    ! [A_216,B_217,C_218] :
      ( k2_relset_1(A_216,B_217,C_218) = k2_relat_1(C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1772,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1766])).

tff(c_1785,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1772])).

tff(c_34,plain,(
    ! [A_10] :
      ( k1_relat_1(k2_funct_1(A_10)) = k2_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_79,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_374,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(A_70,B_71,C_72) = k2_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_377,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_374])).

tff(c_389,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_377])).

tff(c_24,plain,(
    ! [A_8] :
      ( k2_relat_1(A_8) != k1_xboole_0
      | k1_xboole_0 = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_280,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_271,c_24])).

tff(c_311,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_407,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_311])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_391,plain,(
    ! [A_73,B_74,C_75] :
      ( k1_relset_1(A_73,B_74,C_75) = k1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_405,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_391])).

tff(c_623,plain,(
    ! [B_105,A_106,C_107] :
      ( k1_xboole_0 = B_105
      | k1_relset_1(A_106,B_105,C_107) = A_106
      | ~ v1_funct_2(C_107,A_106,B_105)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_629,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_623])).

tff(c_643,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_405,c_629])).

tff(c_644,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_407,c_643])).

tff(c_32,plain,(
    ! [A_10] :
      ( k2_relat_1(k2_funct_1(A_10)) = k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_152,plain,(
    ! [A_36] :
      ( v1_funct_1(k2_funct_1(A_36))
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_68,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_143,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_155,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_152,c_143])).

tff(c_158,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_155])).

tff(c_202,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_205,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_202])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_205])).

tff(c_219,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_416,plain,(
    ! [B_76,A_77] :
      ( v1_funct_2(B_76,k1_relat_1(B_76),A_77)
      | ~ r1_tarski(k2_relat_1(B_76),A_77)
      | ~ v1_funct_1(B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_916,plain,(
    ! [A_127,A_128] :
      ( v1_funct_2(k2_funct_1(A_127),k2_relat_1(A_127),A_128)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_127)),A_128)
      | ~ v1_funct_1(k2_funct_1(A_127))
      | ~ v1_relat_1(k2_funct_1(A_127))
      | ~ v2_funct_1(A_127)
      | ~ v1_funct_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_416])).

tff(c_922,plain,(
    ! [A_128] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_128)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_128)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_916])).

tff(c_931,plain,(
    ! [A_128] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_128)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_128)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_78,c_72,c_219,c_922])).

tff(c_934,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_931])).

tff(c_937,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_934])).

tff(c_941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_78,c_937])).

tff(c_943,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_931])).

tff(c_525,plain,(
    ! [B_92,A_93] :
      ( m1_subset_1(B_92,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_92),A_93)))
      | ~ r1_tarski(k2_relat_1(B_92),A_93)
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_958,plain,(
    ! [A_129,A_130] :
      ( m1_subset_1(k2_funct_1(A_129),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_129),A_130)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_129)),A_130)
      | ~ v1_funct_1(k2_funct_1(A_129))
      | ~ v1_relat_1(k2_funct_1(A_129))
      | ~ v2_funct_1(A_129)
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_525])).

tff(c_976,plain,(
    ! [A_130] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_130)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_130)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_958])).

tff(c_1013,plain,(
    ! [A_132] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_132)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_78,c_72,c_943,c_219,c_976])).

tff(c_218,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_309,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_1040,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1013,c_309])).

tff(c_1045,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1040])).

tff(c_1048,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_78,c_72,c_6,c_644,c_1045])).

tff(c_1049,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1060,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_1049,c_22])).

tff(c_26,plain,(
    ! [A_8] :
      ( k1_relat_1(A_8) != k1_xboole_0
      | k1_xboole_0 = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_279,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_271,c_26])).

tff(c_310,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_1051,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_310])).

tff(c_1088,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1060,c_1051])).

tff(c_1089,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_1090,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_1111,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_1090])).

tff(c_220,plain,(
    ! [A_46] :
      ( v1_relat_1(k2_funct_1(A_46))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_224,plain,(
    ! [A_46] :
      ( k2_relat_1(k2_funct_1(A_46)) != k1_xboole_0
      | k2_funct_1(A_46) = k1_xboole_0
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_220,c_24])).

tff(c_1277,plain,(
    ! [A_154] :
      ( k2_relat_1(k2_funct_1(A_154)) != '#skF_3'
      | k2_funct_1(A_154) = '#skF_3'
      | ~ v1_funct_1(A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_1089,c_224])).

tff(c_1664,plain,(
    ! [A_204] :
      ( k1_relat_1(A_204) != '#skF_3'
      | k2_funct_1(A_204) = '#skF_3'
      | ~ v1_funct_1(A_204)
      | ~ v1_relat_1(A_204)
      | ~ v2_funct_1(A_204)
      | ~ v1_funct_1(A_204)
      | ~ v1_relat_1(A_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1277])).

tff(c_1667,plain,
    ( k1_relat_1('#skF_3') != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1664])).

tff(c_1670,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_78,c_1111,c_1667])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1097,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_1089,c_14])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1100,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_1089,c_20])).

tff(c_1281,plain,(
    ! [A_155,B_156,C_157] :
      ( k2_relset_1(A_155,B_156,C_157) = k2_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1290,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1281])).

tff(c_1296,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1100,c_70,c_1290])).

tff(c_1298,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1296,c_309])).

tff(c_1302,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1097,c_1298])).

tff(c_1671,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1670,c_1302])).

tff(c_1675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_1671])).

tff(c_1676,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_1677,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_1787,plain,(
    ! [A_219,B_220,C_221] :
      ( k1_relset_1(A_219,B_220,C_221) = k1_relat_1(C_221)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1804,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1677,c_1787])).

tff(c_2007,plain,(
    ! [B_248,C_249,A_250] :
      ( k1_xboole_0 = B_248
      | v1_funct_2(C_249,A_250,B_248)
      | k1_relset_1(A_250,B_248,C_249) != A_250
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_250,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2013,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_1677,c_2007])).

tff(c_2029,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1804,c_2013])).

tff(c_2030,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1676,c_2029])).

tff(c_2037,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2030])).

tff(c_2040,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2037])).

tff(c_2043,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_78,c_72,c_1785,c_2040])).

tff(c_2044,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2030])).

tff(c_1691,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_1807,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1785,c_1691])).

tff(c_2060,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2044,c_1807])).

tff(c_1805,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1787])).

tff(c_60,plain,(
    ! [B_22,A_21,C_23] :
      ( k1_xboole_0 = B_22
      | k1_relset_1(A_21,B_22,C_23) = A_21
      | ~ v1_funct_2(C_23,A_21,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2089,plain,(
    ! [B_251,A_252,C_253] :
      ( B_251 = '#skF_1'
      | k1_relset_1(A_252,B_251,C_253) = A_252
      | ~ v1_funct_2(C_253,A_252,B_251)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_252,B_251))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2044,c_60])).

tff(c_2098,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_2089])).

tff(c_2108,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1805,c_2098])).

tff(c_2115,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_2060,c_2108])).

tff(c_1690,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_2069,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2044,c_1690])).

tff(c_2151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2115,c_2069])).

tff(c_2152,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_2154,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2152,c_1690])).

tff(c_2163,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2152,c_2152,c_22])).

tff(c_2197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2154,c_2163])).

tff(c_2198,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2210,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2198,c_8])).

tff(c_2209,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2198,c_2198,c_20])).

tff(c_2199,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_2229,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2198,c_2199])).

tff(c_2526,plain,(
    ! [B_286,A_287] :
      ( v1_funct_2(B_286,k1_relat_1(B_286),A_287)
      | ~ r1_tarski(k2_relat_1(B_286),A_287)
      | ~ v1_funct_1(B_286)
      | ~ v1_relat_1(B_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2535,plain,(
    ! [A_287] :
      ( v1_funct_2('#skF_3','#skF_3',A_287)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_287)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2229,c_2526])).

tff(c_2538,plain,(
    ! [A_287] : v1_funct_2('#skF_3','#skF_3',A_287) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_78,c_2210,c_2209,c_2535])).

tff(c_2462,plain,(
    ! [A_281,B_282,C_283] :
      ( k2_relset_1(A_281,B_282,C_283) = k2_relat_1(C_283)
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2474,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_2462])).

tff(c_2482,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2209,c_2474])).

tff(c_44,plain,(
    ! [C_14,A_12,B_13] :
      ( v1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1681,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1677,c_44])).

tff(c_1688,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0
    | k2_funct_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1681,c_26])).

tff(c_2307,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2198,c_2198,c_1688])).

tff(c_2308,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2307])).

tff(c_2311,plain,
    ( k2_relat_1('#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2308])).

tff(c_2314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_78,c_72,c_2209,c_2311])).

tff(c_2315,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2307])).

tff(c_2319,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2315,c_1676])).

tff(c_2487,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2482,c_2319])).

tff(c_2541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2538,c_2487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:22:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.46/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.77  
% 4.46/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.77  %$ v1_funct_2 > v5_relat_1 > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.46/1.77  
% 4.46/1.77  %Foreground sorts:
% 4.46/1.77  
% 4.46/1.77  
% 4.46/1.77  %Background operators:
% 4.46/1.77  
% 4.46/1.77  
% 4.46/1.77  %Foreground operators:
% 4.46/1.77  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.46/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.46/1.77  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.46/1.77  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.46/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.46/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.46/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.46/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.46/1.77  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 4.46/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.46/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.46/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.46/1.77  tff('#skF_1', type, '#skF_1': $i).
% 4.46/1.77  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.46/1.77  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.46/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.46/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.46/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.46/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.46/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.46/1.77  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.46/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.46/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.46/1.77  
% 4.46/1.80  tff(f_139, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.46/1.80  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.46/1.80  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.46/1.80  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.46/1.80  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.46/1.80  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.46/1.80  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.46/1.80  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.46/1.80  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.46/1.80  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.46/1.80  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.46/1.80  tff(f_122, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.46/1.80  tff(f_46, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.46/1.80  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.46/1.80  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.46/1.80  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.46/1.80  tff(c_259, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.46/1.80  tff(c_271, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_259])).
% 4.46/1.80  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.46/1.80  tff(c_72, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.46/1.80  tff(c_70, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.46/1.80  tff(c_1766, plain, (![A_216, B_217, C_218]: (k2_relset_1(A_216, B_217, C_218)=k2_relat_1(C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.46/1.80  tff(c_1772, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1766])).
% 4.46/1.80  tff(c_1785, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1772])).
% 4.46/1.80  tff(c_34, plain, (![A_10]: (k1_relat_1(k2_funct_1(A_10))=k2_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.46/1.80  tff(c_16, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.46/1.80  tff(c_18, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.46/1.80  tff(c_79, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 4.46/1.80  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.46/1.80  tff(c_374, plain, (![A_70, B_71, C_72]: (k2_relset_1(A_70, B_71, C_72)=k2_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.46/1.80  tff(c_377, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_374])).
% 4.46/1.80  tff(c_389, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_377])).
% 4.46/1.80  tff(c_24, plain, (![A_8]: (k2_relat_1(A_8)!=k1_xboole_0 | k1_xboole_0=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.46/1.80  tff(c_280, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_271, c_24])).
% 4.46/1.80  tff(c_311, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_280])).
% 4.46/1.80  tff(c_407, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_389, c_311])).
% 4.46/1.80  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.46/1.80  tff(c_391, plain, (![A_73, B_74, C_75]: (k1_relset_1(A_73, B_74, C_75)=k1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.46/1.80  tff(c_405, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_391])).
% 4.46/1.80  tff(c_623, plain, (![B_105, A_106, C_107]: (k1_xboole_0=B_105 | k1_relset_1(A_106, B_105, C_107)=A_106 | ~v1_funct_2(C_107, A_106, B_105) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.46/1.80  tff(c_629, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_623])).
% 4.46/1.80  tff(c_643, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_405, c_629])).
% 4.46/1.80  tff(c_644, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_407, c_643])).
% 4.46/1.80  tff(c_32, plain, (![A_10]: (k2_relat_1(k2_funct_1(A_10))=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.46/1.80  tff(c_30, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.46/1.80  tff(c_152, plain, (![A_36]: (v1_funct_1(k2_funct_1(A_36)) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.46/1.80  tff(c_68, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.46/1.80  tff(c_143, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_68])).
% 4.46/1.80  tff(c_155, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_152, c_143])).
% 4.46/1.80  tff(c_158, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_155])).
% 4.46/1.80  tff(c_202, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.46/1.80  tff(c_205, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_202])).
% 4.46/1.80  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_158, c_205])).
% 4.46/1.80  tff(c_219, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_68])).
% 4.46/1.80  tff(c_416, plain, (![B_76, A_77]: (v1_funct_2(B_76, k1_relat_1(B_76), A_77) | ~r1_tarski(k2_relat_1(B_76), A_77) | ~v1_funct_1(B_76) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.46/1.80  tff(c_916, plain, (![A_127, A_128]: (v1_funct_2(k2_funct_1(A_127), k2_relat_1(A_127), A_128) | ~r1_tarski(k2_relat_1(k2_funct_1(A_127)), A_128) | ~v1_funct_1(k2_funct_1(A_127)) | ~v1_relat_1(k2_funct_1(A_127)) | ~v2_funct_1(A_127) | ~v1_funct_1(A_127) | ~v1_relat_1(A_127))), inference(superposition, [status(thm), theory('equality')], [c_34, c_416])).
% 4.46/1.80  tff(c_922, plain, (![A_128]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_128) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_128) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_389, c_916])).
% 4.46/1.80  tff(c_931, plain, (![A_128]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_128) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_128) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_78, c_72, c_219, c_922])).
% 4.46/1.80  tff(c_934, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_931])).
% 4.46/1.80  tff(c_937, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_934])).
% 4.46/1.80  tff(c_941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_271, c_78, c_937])).
% 4.46/1.80  tff(c_943, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_931])).
% 4.46/1.80  tff(c_525, plain, (![B_92, A_93]: (m1_subset_1(B_92, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_92), A_93))) | ~r1_tarski(k2_relat_1(B_92), A_93) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.46/1.80  tff(c_958, plain, (![A_129, A_130]: (m1_subset_1(k2_funct_1(A_129), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_129), A_130))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_129)), A_130) | ~v1_funct_1(k2_funct_1(A_129)) | ~v1_relat_1(k2_funct_1(A_129)) | ~v2_funct_1(A_129) | ~v1_funct_1(A_129) | ~v1_relat_1(A_129))), inference(superposition, [status(thm), theory('equality')], [c_34, c_525])).
% 4.46/1.80  tff(c_976, plain, (![A_130]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_130))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_130) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_389, c_958])).
% 4.46/1.80  tff(c_1013, plain, (![A_132]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_132))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_132))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_78, c_72, c_943, c_219, c_976])).
% 4.46/1.80  tff(c_218, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_68])).
% 4.46/1.80  tff(c_309, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_218])).
% 4.46/1.80  tff(c_1040, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_1013, c_309])).
% 4.46/1.80  tff(c_1045, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_1040])).
% 4.46/1.80  tff(c_1048, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_271, c_78, c_72, c_6, c_644, c_1045])).
% 4.46/1.80  tff(c_1049, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_280])).
% 4.46/1.80  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.46/1.80  tff(c_1060, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1049, c_1049, c_22])).
% 4.46/1.80  tff(c_26, plain, (![A_8]: (k1_relat_1(A_8)!=k1_xboole_0 | k1_xboole_0=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.46/1.80  tff(c_279, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_271, c_26])).
% 4.46/1.80  tff(c_310, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_279])).
% 4.46/1.80  tff(c_1051, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1049, c_310])).
% 4.46/1.80  tff(c_1088, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1060, c_1051])).
% 4.46/1.80  tff(c_1089, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_279])).
% 4.46/1.80  tff(c_1090, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_279])).
% 4.46/1.80  tff(c_1111, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_1090])).
% 4.46/1.80  tff(c_220, plain, (![A_46]: (v1_relat_1(k2_funct_1(A_46)) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.46/1.80  tff(c_224, plain, (![A_46]: (k2_relat_1(k2_funct_1(A_46))!=k1_xboole_0 | k2_funct_1(A_46)=k1_xboole_0 | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_220, c_24])).
% 4.46/1.80  tff(c_1277, plain, (![A_154]: (k2_relat_1(k2_funct_1(A_154))!='#skF_3' | k2_funct_1(A_154)='#skF_3' | ~v1_funct_1(A_154) | ~v1_relat_1(A_154))), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_1089, c_224])).
% 4.46/1.80  tff(c_1664, plain, (![A_204]: (k1_relat_1(A_204)!='#skF_3' | k2_funct_1(A_204)='#skF_3' | ~v1_funct_1(A_204) | ~v1_relat_1(A_204) | ~v2_funct_1(A_204) | ~v1_funct_1(A_204) | ~v1_relat_1(A_204))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1277])).
% 4.46/1.80  tff(c_1667, plain, (k1_relat_1('#skF_3')!='#skF_3' | k2_funct_1('#skF_3')='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1664])).
% 4.46/1.80  tff(c_1670, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_271, c_78, c_1111, c_1667])).
% 4.46/1.80  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.46/1.80  tff(c_1097, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_1089, c_14])).
% 4.46/1.80  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.46/1.80  tff(c_1100, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_1089, c_20])).
% 4.46/1.80  tff(c_1281, plain, (![A_155, B_156, C_157]: (k2_relset_1(A_155, B_156, C_157)=k2_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.46/1.80  tff(c_1290, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1281])).
% 4.46/1.80  tff(c_1296, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1100, c_70, c_1290])).
% 4.46/1.80  tff(c_1298, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1296, c_309])).
% 4.46/1.80  tff(c_1302, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1097, c_1298])).
% 4.46/1.80  tff(c_1671, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1670, c_1302])).
% 4.46/1.80  tff(c_1675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_1671])).
% 4.46/1.80  tff(c_1676, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_218])).
% 4.46/1.80  tff(c_1677, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_218])).
% 4.46/1.80  tff(c_1787, plain, (![A_219, B_220, C_221]: (k1_relset_1(A_219, B_220, C_221)=k1_relat_1(C_221) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.46/1.80  tff(c_1804, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1677, c_1787])).
% 4.46/1.80  tff(c_2007, plain, (![B_248, C_249, A_250]: (k1_xboole_0=B_248 | v1_funct_2(C_249, A_250, B_248) | k1_relset_1(A_250, B_248, C_249)!=A_250 | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_250, B_248))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.46/1.80  tff(c_2013, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_1677, c_2007])).
% 4.46/1.80  tff(c_2029, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1804, c_2013])).
% 4.46/1.80  tff(c_2030, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1676, c_2029])).
% 4.46/1.80  tff(c_2037, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_2030])).
% 4.46/1.80  tff(c_2040, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_2037])).
% 4.46/1.80  tff(c_2043, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_271, c_78, c_72, c_1785, c_2040])).
% 4.46/1.80  tff(c_2044, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_2030])).
% 4.46/1.80  tff(c_1691, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_280])).
% 4.46/1.80  tff(c_1807, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1785, c_1691])).
% 4.46/1.80  tff(c_2060, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2044, c_1807])).
% 4.46/1.80  tff(c_1805, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1787])).
% 4.46/1.80  tff(c_60, plain, (![B_22, A_21, C_23]: (k1_xboole_0=B_22 | k1_relset_1(A_21, B_22, C_23)=A_21 | ~v1_funct_2(C_23, A_21, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.46/1.80  tff(c_2089, plain, (![B_251, A_252, C_253]: (B_251='#skF_1' | k1_relset_1(A_252, B_251, C_253)=A_252 | ~v1_funct_2(C_253, A_252, B_251) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_252, B_251))))), inference(demodulation, [status(thm), theory('equality')], [c_2044, c_60])).
% 4.46/1.80  tff(c_2098, plain, ('#skF_2'='#skF_1' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_2089])).
% 4.46/1.80  tff(c_2108, plain, ('#skF_2'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1805, c_2098])).
% 4.46/1.80  tff(c_2115, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_2060, c_2108])).
% 4.46/1.80  tff(c_1690, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_279])).
% 4.46/1.80  tff(c_2069, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2044, c_1690])).
% 4.46/1.80  tff(c_2151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2115, c_2069])).
% 4.46/1.80  tff(c_2152, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_280])).
% 4.46/1.80  tff(c_2154, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2152, c_1690])).
% 4.46/1.80  tff(c_2163, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2152, c_2152, c_22])).
% 4.46/1.80  tff(c_2197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2154, c_2163])).
% 4.46/1.80  tff(c_2198, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_279])).
% 4.46/1.80  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.46/1.80  tff(c_2210, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2198, c_8])).
% 4.46/1.80  tff(c_2209, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2198, c_2198, c_20])).
% 4.46/1.80  tff(c_2199, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_279])).
% 4.46/1.80  tff(c_2229, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2198, c_2199])).
% 4.46/1.80  tff(c_2526, plain, (![B_286, A_287]: (v1_funct_2(B_286, k1_relat_1(B_286), A_287) | ~r1_tarski(k2_relat_1(B_286), A_287) | ~v1_funct_1(B_286) | ~v1_relat_1(B_286))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.46/1.80  tff(c_2535, plain, (![A_287]: (v1_funct_2('#skF_3', '#skF_3', A_287) | ~r1_tarski(k2_relat_1('#skF_3'), A_287) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2229, c_2526])).
% 4.46/1.80  tff(c_2538, plain, (![A_287]: (v1_funct_2('#skF_3', '#skF_3', A_287))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_78, c_2210, c_2209, c_2535])).
% 4.46/1.80  tff(c_2462, plain, (![A_281, B_282, C_283]: (k2_relset_1(A_281, B_282, C_283)=k2_relat_1(C_283) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.46/1.80  tff(c_2474, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_2462])).
% 4.46/1.80  tff(c_2482, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2209, c_2474])).
% 4.46/1.80  tff(c_44, plain, (![C_14, A_12, B_13]: (v1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.46/1.80  tff(c_1681, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1677, c_44])).
% 4.46/1.80  tff(c_1688, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0 | k2_funct_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1681, c_26])).
% 4.46/1.80  tff(c_2307, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2198, c_2198, c_1688])).
% 4.46/1.80  tff(c_2308, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_2307])).
% 4.46/1.80  tff(c_2311, plain, (k2_relat_1('#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_2308])).
% 4.46/1.80  tff(c_2314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_271, c_78, c_72, c_2209, c_2311])).
% 4.46/1.80  tff(c_2315, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_2307])).
% 4.46/1.80  tff(c_2319, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2315, c_1676])).
% 4.46/1.80  tff(c_2487, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2482, c_2319])).
% 4.46/1.80  tff(c_2541, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2538, c_2487])).
% 4.46/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.80  
% 4.46/1.80  Inference rules
% 4.46/1.80  ----------------------
% 4.46/1.80  #Ref     : 0
% 4.46/1.80  #Sup     : 520
% 4.46/1.80  #Fact    : 0
% 4.46/1.80  #Define  : 0
% 4.46/1.80  #Split   : 16
% 4.46/1.80  #Chain   : 0
% 4.46/1.80  #Close   : 0
% 4.46/1.80  
% 4.46/1.80  Ordering : KBO
% 4.46/1.80  
% 4.46/1.80  Simplification rules
% 4.46/1.80  ----------------------
% 4.46/1.80  #Subsume      : 43
% 4.46/1.80  #Demod        : 736
% 4.46/1.80  #Tautology    : 329
% 4.46/1.80  #SimpNegUnit  : 9
% 4.46/1.80  #BackRed      : 120
% 4.46/1.80  
% 4.46/1.80  #Partial instantiations: 0
% 4.46/1.80  #Strategies tried      : 1
% 4.46/1.80  
% 4.46/1.80  Timing (in seconds)
% 4.46/1.80  ----------------------
% 4.46/1.80  Preprocessing        : 0.34
% 4.46/1.80  Parsing              : 0.18
% 4.46/1.80  CNF conversion       : 0.02
% 4.46/1.80  Main loop            : 0.66
% 4.46/1.80  Inferencing          : 0.23
% 4.46/1.80  Reduction            : 0.23
% 4.46/1.80  Demodulation         : 0.16
% 4.46/1.80  BG Simplification    : 0.03
% 4.46/1.80  Subsumption          : 0.11
% 4.46/1.80  Abstraction          : 0.03
% 4.46/1.80  MUC search           : 0.00
% 4.46/1.80  Cooper               : 0.00
% 4.46/1.80  Total                : 1.05
% 4.46/1.80  Index Insertion      : 0.00
% 4.46/1.80  Index Deletion       : 0.00
% 4.46/1.80  Index Matching       : 0.00
% 4.46/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
