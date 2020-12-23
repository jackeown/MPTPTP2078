%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:59 EST 2020

% Result     : Theorem 4.18s
% Output     : CNFRefutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 705 expanded)
%              Number of leaves         :   30 ( 235 expanded)
%              Depth                    :   15
%              Number of atoms          :  333 (2480 expanded)
%              Number of equality atoms :   81 ( 858 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ( B = k1_xboole_0
               => A = k1_xboole_0 )
             => ( r1_partfun1(C,D)
              <=> ! [E] :
                    ( r2_hidden(E,k1_relset_1(A,B,C))
                   => k1_funct_1(C,E) = k1_funct_1(D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_2)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
           => ( r1_partfun1(A,B)
            <=> ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).

tff(c_46,plain,
    ( r2_hidden('#skF_6',k1_relset_1('#skF_2','#skF_3','#skF_4'))
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_66,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_72,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_81,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_72])).

tff(c_88,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_81])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_78,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_72])).

tff(c_85,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_78])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_110,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_123,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_110])).

tff(c_133,plain,(
    ! [A_51,B_52,C_53] :
      ( m1_subset_1(k1_relset_1(A_51,B_52,C_53),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_146,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_133])).

tff(c_154,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_146])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_164,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_154,c_2])).

tff(c_32,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_55,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_36,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_122,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_110])).

tff(c_364,plain,(
    ! [B_88,A_89,C_90] :
      ( k1_xboole_0 = B_88
      | k1_relset_1(A_89,B_88,C_90) = A_89
      | ~ v1_funct_2(C_90,A_89,B_88)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_375,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_364])).

tff(c_383,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_122,c_375])).

tff(c_384,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_383])).

tff(c_388,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_1'(A_91,B_92),k1_relat_1(A_91))
      | r1_partfun1(A_91,B_92)
      | ~ r1_tarski(k1_relat_1(A_91),k1_relat_1(B_92))
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_54,plain,(
    ! [E_34] :
      ( r1_partfun1('#skF_4','#skF_5')
      | k1_funct_1('#skF_5',E_34) = k1_funct_1('#skF_4',E_34)
      | ~ r2_hidden(E_34,k1_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_102,plain,(
    ! [E_34] :
      ( k1_funct_1('#skF_5',E_34) = k1_funct_1('#skF_4',E_34)
      | ~ r2_hidden(E_34,k1_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_54])).

tff(c_128,plain,(
    ! [E_34] :
      ( k1_funct_1('#skF_5',E_34) = k1_funct_1('#skF_4',E_34)
      | ~ r2_hidden(E_34,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_102])).

tff(c_392,plain,(
    ! [B_92] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_92)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_92))
      | r1_partfun1('#skF_4',B_92)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_92))
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_388,c_128])).

tff(c_520,plain,(
    ! [B_114] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_114)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_114))
      | r1_partfun1('#skF_4',B_114)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_114))
      | ~ v1_funct_1(B_114)
      | ~ v1_relat_1(B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_42,c_392])).

tff(c_523,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_520])).

tff(c_525,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_38,c_164,c_523])).

tff(c_526,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_525])).

tff(c_553,plain,(
    ! [B_126,A_127] :
      ( k1_funct_1(B_126,'#skF_1'(A_127,B_126)) != k1_funct_1(A_127,'#skF_1'(A_127,B_126))
      | r1_partfun1(A_127,B_126)
      | ~ r1_tarski(k1_relat_1(A_127),k1_relat_1(B_126))
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_funct_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_555,plain,
    ( r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_553])).

tff(c_558,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_42,c_85,c_38,c_164,c_384,c_555])).

tff(c_560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_558])).

tff(c_562,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,
    ( k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_564,plain,(
    k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_44])).

tff(c_570,plain,(
    ! [B_130,A_131] :
      ( v1_relat_1(B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_131))
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_576,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_570])).

tff(c_583,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_576])).

tff(c_606,plain,(
    ! [A_136,B_137,C_138] :
      ( k1_relset_1(A_136,B_137,C_138) = k1_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_619,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_606])).

tff(c_641,plain,(
    ! [A_142,B_143,C_144] :
      ( m1_subset_1(k1_relset_1(A_142,B_143,C_144),k1_zfmisc_1(A_142))
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_654,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_641])).

tff(c_662,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_654])).

tff(c_683,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_662,c_2])).

tff(c_618,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_606])).

tff(c_841,plain,(
    ! [B_172,A_173,C_174] :
      ( k1_xboole_0 = B_172
      | k1_relset_1(A_173,B_172,C_174) = A_173
      | ~ v1_funct_2(C_174,A_173,B_172)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_173,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_852,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_841])).

tff(c_860,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_618,c_852])).

tff(c_861,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_860])).

tff(c_579,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_570])).

tff(c_586,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_579])).

tff(c_561,plain,(
    r2_hidden('#skF_6',k1_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_625,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_561])).

tff(c_946,plain,(
    ! [B_184,C_185,A_186] :
      ( k1_funct_1(B_184,C_185) = k1_funct_1(A_186,C_185)
      | ~ r2_hidden(C_185,k1_relat_1(A_186))
      | ~ r1_partfun1(A_186,B_184)
      | ~ r1_tarski(k1_relat_1(A_186),k1_relat_1(B_184))
      | ~ v1_funct_1(B_184)
      | ~ v1_relat_1(B_184)
      | ~ v1_funct_1(A_186)
      | ~ v1_relat_1(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_952,plain,(
    ! [B_184] :
      ( k1_funct_1(B_184,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_184)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_184))
      | ~ v1_funct_1(B_184)
      | ~ v1_relat_1(B_184)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_625,c_946])).

tff(c_959,plain,(
    ! [B_187] :
      ( k1_funct_1(B_187,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_187)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_187))
      | ~ v1_funct_1(B_187)
      | ~ v1_relat_1(B_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_42,c_952])).

tff(c_962,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_861,c_959])).

tff(c_964,plain,(
    k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_38,c_683,c_562,c_962])).

tff(c_966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_564,c_964])).

tff(c_968,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_967,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_973,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_967])).

tff(c_995,plain,
    ( r2_hidden('#skF_6',k1_relset_1('#skF_3','#skF_3','#skF_4'))
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_46])).

tff(c_996,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_995])).

tff(c_984,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_40])).

tff(c_1002,plain,(
    ! [B_194,A_195] :
      ( v1_relat_1(B_194)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(A_195))
      | ~ v1_relat_1(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1011,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_984,c_1002])).

tff(c_1018,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1011])).

tff(c_985,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_34])).

tff(c_1008,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_985,c_1002])).

tff(c_1015,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1008])).

tff(c_1042,plain,(
    ! [A_201,B_202,C_203] :
      ( k1_relset_1(A_201,B_202,C_203) = k1_relat_1(C_203)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1055,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_984,c_1042])).

tff(c_1065,plain,(
    ! [A_204,B_205,C_206] :
      ( m1_subset_1(k1_relset_1(A_204,B_205,C_206),k1_zfmisc_1(A_204))
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1078,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_1065])).

tff(c_1086,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_1078])).

tff(c_1096,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1086,c_2])).

tff(c_978,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_36])).

tff(c_1054,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_985,c_1042])).

tff(c_22,plain,(
    ! [B_15,C_16] :
      ( k1_relset_1(k1_xboole_0,B_15,C_16) = k1_xboole_0
      | ~ v1_funct_2(C_16,k1_xboole_0,B_15)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1225,plain,(
    ! [B_224,C_225] :
      ( k1_relset_1('#skF_3',B_224,C_225) = '#skF_3'
      | ~ v1_funct_2(C_225,'#skF_3',B_224)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_224))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_968,c_968,c_968,c_22])).

tff(c_1236,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_985,c_1225])).

tff(c_1244,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_978,c_1054,c_1236])).

tff(c_1504,plain,(
    ! [A_259,B_260] :
      ( r2_hidden('#skF_1'(A_259,B_260),k1_relat_1(A_259))
      | r1_partfun1(A_259,B_260)
      | ~ r1_tarski(k1_relat_1(A_259),k1_relat_1(B_260))
      | ~ v1_funct_1(B_260)
      | ~ v1_relat_1(B_260)
      | ~ v1_funct_1(A_259)
      | ~ v1_relat_1(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1032,plain,(
    ! [E_34] :
      ( r1_partfun1('#skF_4','#skF_5')
      | k1_funct_1('#skF_5',E_34) = k1_funct_1('#skF_4',E_34)
      | ~ r2_hidden(E_34,k1_relset_1('#skF_3','#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_54])).

tff(c_1033,plain,(
    ! [E_34] :
      ( k1_funct_1('#skF_5',E_34) = k1_funct_1('#skF_4',E_34)
      | ~ r2_hidden(E_34,k1_relset_1('#skF_3','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_996,c_1032])).

tff(c_1060,plain,(
    ! [E_34] :
      ( k1_funct_1('#skF_5',E_34) = k1_funct_1('#skF_4',E_34)
      | ~ r2_hidden(E_34,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_1033])).

tff(c_1508,plain,(
    ! [B_260] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_260)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_260))
      | r1_partfun1('#skF_4',B_260)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_260))
      | ~ v1_funct_1(B_260)
      | ~ v1_relat_1(B_260)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1504,c_1060])).

tff(c_1518,plain,(
    ! [B_262] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_262)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_262))
      | r1_partfun1('#skF_4',B_262)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_262))
      | ~ v1_funct_1(B_262)
      | ~ v1_relat_1(B_262) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_42,c_1508])).

tff(c_1521,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1244,c_1518])).

tff(c_1523,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1015,c_38,c_1096,c_1521])).

tff(c_1524,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_996,c_1523])).

tff(c_1563,plain,(
    ! [B_279,A_280] :
      ( k1_funct_1(B_279,'#skF_1'(A_280,B_279)) != k1_funct_1(A_280,'#skF_1'(A_280,B_279))
      | r1_partfun1(A_280,B_279)
      | ~ r1_tarski(k1_relat_1(A_280),k1_relat_1(B_279))
      | ~ v1_funct_1(B_279)
      | ~ v1_relat_1(B_279)
      | ~ v1_funct_1(A_280)
      | ~ v1_relat_1(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1565,plain,
    ( r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1524,c_1563])).

tff(c_1568,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_42,c_1015,c_38,c_1096,c_1244,c_1565])).

tff(c_1570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_996,c_1568])).

tff(c_1572,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_995])).

tff(c_1574,plain,(
    k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1572,c_44])).

tff(c_1580,plain,(
    ! [B_283,A_284] :
      ( v1_relat_1(B_283)
      | ~ m1_subset_1(B_283,k1_zfmisc_1(A_284))
      | ~ v1_relat_1(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1586,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_985,c_1580])).

tff(c_1593,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1586])).

tff(c_1610,plain,(
    ! [A_287,B_288,C_289] :
      ( k1_relset_1(A_287,B_288,C_289) = k1_relat_1(C_289)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1623,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_984,c_1610])).

tff(c_1652,plain,(
    ! [A_295,B_296,C_297] :
      ( m1_subset_1(k1_relset_1(A_295,B_296,C_297),k1_zfmisc_1(A_295))
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_295,B_296))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1665,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1623,c_1652])).

tff(c_1673,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_1665])).

tff(c_1683,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1673,c_2])).

tff(c_1622,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_985,c_1610])).

tff(c_1727,plain,(
    ! [B_300,C_301] :
      ( k1_relset_1('#skF_3',B_300,C_301) = '#skF_3'
      | ~ v1_funct_2(C_301,'#skF_3',B_300)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_300))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_968,c_968,c_968,c_22])).

tff(c_1738,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_985,c_1727])).

tff(c_1746,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_978,c_1622,c_1738])).

tff(c_1589,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_984,c_1580])).

tff(c_1596,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1589])).

tff(c_1571,plain,(
    r2_hidden('#skF_6',k1_relset_1('#skF_3','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_995])).

tff(c_1628,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1623,c_1571])).

tff(c_2070,plain,(
    ! [B_341,C_342,A_343] :
      ( k1_funct_1(B_341,C_342) = k1_funct_1(A_343,C_342)
      | ~ r2_hidden(C_342,k1_relat_1(A_343))
      | ~ r1_partfun1(A_343,B_341)
      | ~ r1_tarski(k1_relat_1(A_343),k1_relat_1(B_341))
      | ~ v1_funct_1(B_341)
      | ~ v1_relat_1(B_341)
      | ~ v1_funct_1(A_343)
      | ~ v1_relat_1(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2076,plain,(
    ! [B_341] :
      ( k1_funct_1(B_341,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_341)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_341))
      | ~ v1_funct_1(B_341)
      | ~ v1_relat_1(B_341)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1628,c_2070])).

tff(c_2083,plain,(
    ! [B_344] :
      ( k1_funct_1(B_344,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_344)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_344))
      | ~ v1_funct_1(B_344)
      | ~ v1_relat_1(B_344) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1596,c_42,c_2076])).

tff(c_2086,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1746,c_2083])).

tff(c_2088,plain,(
    k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1593,c_38,c_1683,c_1572,c_2086])).

tff(c_2090,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1574,c_2088])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:56:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.18/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/1.77  
% 4.18/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/1.77  %$ v1_funct_2 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.18/1.77  
% 4.18/1.77  %Foreground sorts:
% 4.18/1.77  
% 4.18/1.77  
% 4.18/1.77  %Background operators:
% 4.18/1.77  
% 4.18/1.77  
% 4.18/1.77  %Foreground operators:
% 4.18/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.18/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.18/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.18/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.18/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.18/1.77  tff('#skF_5', type, '#skF_5': $i).
% 4.18/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.18/1.77  tff('#skF_6', type, '#skF_6': $i).
% 4.18/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.18/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.18/1.77  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.18/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.18/1.77  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.18/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.18/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.18/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.18/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.18/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.18/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.18/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.18/1.77  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 4.18/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.18/1.77  
% 4.18/1.80  tff(f_105, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (r1_partfun1(C, D) <=> (![E]: (r2_hidden(E, k1_relset_1(A, B, C)) => (k1_funct_1(C, E) = k1_funct_1(D, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_2)).
% 4.18/1.80  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.18/1.80  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.18/1.80  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.18/1.80  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.18/1.80  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.18/1.80  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.18/1.80  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) => (r1_partfun1(A, B) <=> (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_partfun1)).
% 4.18/1.80  tff(c_46, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.18/1.80  tff(c_66, plain, (~r1_partfun1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_46])).
% 4.18/1.80  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.18/1.80  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.18/1.80  tff(c_72, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.18/1.80  tff(c_81, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_72])).
% 4.18/1.80  tff(c_88, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_81])).
% 4.18/1.80  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.18/1.80  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.18/1.80  tff(c_78, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_72])).
% 4.18/1.80  tff(c_85, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_78])).
% 4.18/1.80  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.18/1.80  tff(c_110, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.18/1.80  tff(c_123, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_110])).
% 4.18/1.80  tff(c_133, plain, (![A_51, B_52, C_53]: (m1_subset_1(k1_relset_1(A_51, B_52, C_53), k1_zfmisc_1(A_51)) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.18/1.80  tff(c_146, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_123, c_133])).
% 4.18/1.80  tff(c_154, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_146])).
% 4.18/1.80  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.18/1.80  tff(c_164, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_154, c_2])).
% 4.18/1.80  tff(c_32, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.18/1.80  tff(c_55, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_32])).
% 4.18/1.80  tff(c_36, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.18/1.80  tff(c_122, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_110])).
% 4.18/1.80  tff(c_364, plain, (![B_88, A_89, C_90]: (k1_xboole_0=B_88 | k1_relset_1(A_89, B_88, C_90)=A_89 | ~v1_funct_2(C_90, A_89, B_88) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.18/1.80  tff(c_375, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_364])).
% 4.18/1.80  tff(c_383, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_122, c_375])).
% 4.18/1.80  tff(c_384, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_55, c_383])).
% 4.18/1.80  tff(c_388, plain, (![A_91, B_92]: (r2_hidden('#skF_1'(A_91, B_92), k1_relat_1(A_91)) | r1_partfun1(A_91, B_92) | ~r1_tarski(k1_relat_1(A_91), k1_relat_1(B_92)) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.18/1.80  tff(c_54, plain, (![E_34]: (r1_partfun1('#skF_4', '#skF_5') | k1_funct_1('#skF_5', E_34)=k1_funct_1('#skF_4', E_34) | ~r2_hidden(E_34, k1_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.18/1.80  tff(c_102, plain, (![E_34]: (k1_funct_1('#skF_5', E_34)=k1_funct_1('#skF_4', E_34) | ~r2_hidden(E_34, k1_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_54])).
% 4.18/1.80  tff(c_128, plain, (![E_34]: (k1_funct_1('#skF_5', E_34)=k1_funct_1('#skF_4', E_34) | ~r2_hidden(E_34, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_102])).
% 4.18/1.80  tff(c_392, plain, (![B_92]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_92))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_92)) | r1_partfun1('#skF_4', B_92) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_92)) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_388, c_128])).
% 4.18/1.80  tff(c_520, plain, (![B_114]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_114))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_114)) | r1_partfun1('#skF_4', B_114) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_114)) | ~v1_funct_1(B_114) | ~v1_relat_1(B_114))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_42, c_392])).
% 4.18/1.80  tff(c_523, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_384, c_520])).
% 4.18/1.80  tff(c_525, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_38, c_164, c_523])).
% 4.18/1.80  tff(c_526, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_525])).
% 4.18/1.80  tff(c_553, plain, (![B_126, A_127]: (k1_funct_1(B_126, '#skF_1'(A_127, B_126))!=k1_funct_1(A_127, '#skF_1'(A_127, B_126)) | r1_partfun1(A_127, B_126) | ~r1_tarski(k1_relat_1(A_127), k1_relat_1(B_126)) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | ~v1_funct_1(A_127) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.18/1.80  tff(c_555, plain, (r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_526, c_553])).
% 4.18/1.80  tff(c_558, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_42, c_85, c_38, c_164, c_384, c_555])).
% 4.18/1.80  tff(c_560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_558])).
% 4.18/1.80  tff(c_562, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 4.18/1.80  tff(c_44, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.18/1.80  tff(c_564, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_562, c_44])).
% 4.18/1.80  tff(c_570, plain, (![B_130, A_131]: (v1_relat_1(B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(A_131)) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.18/1.80  tff(c_576, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_570])).
% 4.18/1.80  tff(c_583, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_576])).
% 4.18/1.80  tff(c_606, plain, (![A_136, B_137, C_138]: (k1_relset_1(A_136, B_137, C_138)=k1_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.18/1.80  tff(c_619, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_606])).
% 4.18/1.80  tff(c_641, plain, (![A_142, B_143, C_144]: (m1_subset_1(k1_relset_1(A_142, B_143, C_144), k1_zfmisc_1(A_142)) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.18/1.80  tff(c_654, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_619, c_641])).
% 4.18/1.80  tff(c_662, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_654])).
% 4.18/1.80  tff(c_683, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_662, c_2])).
% 4.18/1.80  tff(c_618, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_606])).
% 4.18/1.80  tff(c_841, plain, (![B_172, A_173, C_174]: (k1_xboole_0=B_172 | k1_relset_1(A_173, B_172, C_174)=A_173 | ~v1_funct_2(C_174, A_173, B_172) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_173, B_172))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.18/1.80  tff(c_852, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_841])).
% 4.18/1.80  tff(c_860, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_618, c_852])).
% 4.18/1.80  tff(c_861, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_55, c_860])).
% 4.18/1.80  tff(c_579, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_570])).
% 4.18/1.80  tff(c_586, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_579])).
% 4.18/1.80  tff(c_561, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_46])).
% 4.18/1.80  tff(c_625, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_619, c_561])).
% 4.18/1.80  tff(c_946, plain, (![B_184, C_185, A_186]: (k1_funct_1(B_184, C_185)=k1_funct_1(A_186, C_185) | ~r2_hidden(C_185, k1_relat_1(A_186)) | ~r1_partfun1(A_186, B_184) | ~r1_tarski(k1_relat_1(A_186), k1_relat_1(B_184)) | ~v1_funct_1(B_184) | ~v1_relat_1(B_184) | ~v1_funct_1(A_186) | ~v1_relat_1(A_186))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.18/1.80  tff(c_952, plain, (![B_184]: (k1_funct_1(B_184, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_184) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_184)) | ~v1_funct_1(B_184) | ~v1_relat_1(B_184) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_625, c_946])).
% 4.18/1.80  tff(c_959, plain, (![B_187]: (k1_funct_1(B_187, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_187) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_187)) | ~v1_funct_1(B_187) | ~v1_relat_1(B_187))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_42, c_952])).
% 4.18/1.80  tff(c_962, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_861, c_959])).
% 4.18/1.80  tff(c_964, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_583, c_38, c_683, c_562, c_962])).
% 4.18/1.80  tff(c_966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_564, c_964])).
% 4.18/1.80  tff(c_968, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 4.18/1.80  tff(c_967, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 4.18/1.80  tff(c_973, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_968, c_967])).
% 4.18/1.80  tff(c_995, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_3', '#skF_3', '#skF_4')) | ~r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_973, c_46])).
% 4.18/1.80  tff(c_996, plain, (~r1_partfun1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_995])).
% 4.18/1.80  tff(c_984, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_973, c_40])).
% 4.18/1.80  tff(c_1002, plain, (![B_194, A_195]: (v1_relat_1(B_194) | ~m1_subset_1(B_194, k1_zfmisc_1(A_195)) | ~v1_relat_1(A_195))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.18/1.80  tff(c_1011, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_984, c_1002])).
% 4.18/1.80  tff(c_1018, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1011])).
% 4.18/1.80  tff(c_985, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_973, c_34])).
% 4.18/1.80  tff(c_1008, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_985, c_1002])).
% 4.18/1.80  tff(c_1015, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1008])).
% 4.18/1.80  tff(c_1042, plain, (![A_201, B_202, C_203]: (k1_relset_1(A_201, B_202, C_203)=k1_relat_1(C_203) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.18/1.80  tff(c_1055, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_984, c_1042])).
% 4.18/1.80  tff(c_1065, plain, (![A_204, B_205, C_206]: (m1_subset_1(k1_relset_1(A_204, B_205, C_206), k1_zfmisc_1(A_204)) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.18/1.80  tff(c_1078, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1055, c_1065])).
% 4.18/1.80  tff(c_1086, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_984, c_1078])).
% 4.18/1.80  tff(c_1096, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1086, c_2])).
% 4.18/1.80  tff(c_978, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_973, c_36])).
% 4.18/1.80  tff(c_1054, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_985, c_1042])).
% 4.18/1.80  tff(c_22, plain, (![B_15, C_16]: (k1_relset_1(k1_xboole_0, B_15, C_16)=k1_xboole_0 | ~v1_funct_2(C_16, k1_xboole_0, B_15) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_15))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.18/1.80  tff(c_1225, plain, (![B_224, C_225]: (k1_relset_1('#skF_3', B_224, C_225)='#skF_3' | ~v1_funct_2(C_225, '#skF_3', B_224) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_224))))), inference(demodulation, [status(thm), theory('equality')], [c_968, c_968, c_968, c_968, c_22])).
% 4.18/1.80  tff(c_1236, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_985, c_1225])).
% 4.18/1.80  tff(c_1244, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_978, c_1054, c_1236])).
% 4.18/1.80  tff(c_1504, plain, (![A_259, B_260]: (r2_hidden('#skF_1'(A_259, B_260), k1_relat_1(A_259)) | r1_partfun1(A_259, B_260) | ~r1_tarski(k1_relat_1(A_259), k1_relat_1(B_260)) | ~v1_funct_1(B_260) | ~v1_relat_1(B_260) | ~v1_funct_1(A_259) | ~v1_relat_1(A_259))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.18/1.80  tff(c_1032, plain, (![E_34]: (r1_partfun1('#skF_4', '#skF_5') | k1_funct_1('#skF_5', E_34)=k1_funct_1('#skF_4', E_34) | ~r2_hidden(E_34, k1_relset_1('#skF_3', '#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_973, c_54])).
% 4.18/1.80  tff(c_1033, plain, (![E_34]: (k1_funct_1('#skF_5', E_34)=k1_funct_1('#skF_4', E_34) | ~r2_hidden(E_34, k1_relset_1('#skF_3', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_996, c_1032])).
% 4.18/1.80  tff(c_1060, plain, (![E_34]: (k1_funct_1('#skF_5', E_34)=k1_funct_1('#skF_4', E_34) | ~r2_hidden(E_34, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_1033])).
% 4.18/1.80  tff(c_1508, plain, (![B_260]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_260))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_260)) | r1_partfun1('#skF_4', B_260) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_260)) | ~v1_funct_1(B_260) | ~v1_relat_1(B_260) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1504, c_1060])).
% 4.18/1.80  tff(c_1518, plain, (![B_262]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_262))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_262)) | r1_partfun1('#skF_4', B_262) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_262)) | ~v1_funct_1(B_262) | ~v1_relat_1(B_262))), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_42, c_1508])).
% 4.18/1.80  tff(c_1521, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1244, c_1518])).
% 4.18/1.80  tff(c_1523, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1015, c_38, c_1096, c_1521])).
% 4.18/1.80  tff(c_1524, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_996, c_1523])).
% 4.18/1.80  tff(c_1563, plain, (![B_279, A_280]: (k1_funct_1(B_279, '#skF_1'(A_280, B_279))!=k1_funct_1(A_280, '#skF_1'(A_280, B_279)) | r1_partfun1(A_280, B_279) | ~r1_tarski(k1_relat_1(A_280), k1_relat_1(B_279)) | ~v1_funct_1(B_279) | ~v1_relat_1(B_279) | ~v1_funct_1(A_280) | ~v1_relat_1(A_280))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.18/1.80  tff(c_1565, plain, (r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1524, c_1563])).
% 4.18/1.80  tff(c_1568, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_42, c_1015, c_38, c_1096, c_1244, c_1565])).
% 4.18/1.80  tff(c_1570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_996, c_1568])).
% 4.18/1.80  tff(c_1572, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_995])).
% 4.18/1.80  tff(c_1574, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1572, c_44])).
% 4.18/1.80  tff(c_1580, plain, (![B_283, A_284]: (v1_relat_1(B_283) | ~m1_subset_1(B_283, k1_zfmisc_1(A_284)) | ~v1_relat_1(A_284))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.18/1.80  tff(c_1586, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_985, c_1580])).
% 4.18/1.80  tff(c_1593, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1586])).
% 4.18/1.80  tff(c_1610, plain, (![A_287, B_288, C_289]: (k1_relset_1(A_287, B_288, C_289)=k1_relat_1(C_289) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.18/1.80  tff(c_1623, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_984, c_1610])).
% 4.18/1.80  tff(c_1652, plain, (![A_295, B_296, C_297]: (m1_subset_1(k1_relset_1(A_295, B_296, C_297), k1_zfmisc_1(A_295)) | ~m1_subset_1(C_297, k1_zfmisc_1(k2_zfmisc_1(A_295, B_296))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.18/1.80  tff(c_1665, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1623, c_1652])).
% 4.18/1.80  tff(c_1673, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_984, c_1665])).
% 4.18/1.80  tff(c_1683, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1673, c_2])).
% 4.18/1.80  tff(c_1622, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_985, c_1610])).
% 4.18/1.80  tff(c_1727, plain, (![B_300, C_301]: (k1_relset_1('#skF_3', B_300, C_301)='#skF_3' | ~v1_funct_2(C_301, '#skF_3', B_300) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_300))))), inference(demodulation, [status(thm), theory('equality')], [c_968, c_968, c_968, c_968, c_22])).
% 4.18/1.80  tff(c_1738, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_985, c_1727])).
% 4.18/1.80  tff(c_1746, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_978, c_1622, c_1738])).
% 4.18/1.80  tff(c_1589, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_984, c_1580])).
% 4.18/1.80  tff(c_1596, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1589])).
% 4.18/1.80  tff(c_1571, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_3', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_995])).
% 4.18/1.80  tff(c_1628, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1623, c_1571])).
% 4.18/1.80  tff(c_2070, plain, (![B_341, C_342, A_343]: (k1_funct_1(B_341, C_342)=k1_funct_1(A_343, C_342) | ~r2_hidden(C_342, k1_relat_1(A_343)) | ~r1_partfun1(A_343, B_341) | ~r1_tarski(k1_relat_1(A_343), k1_relat_1(B_341)) | ~v1_funct_1(B_341) | ~v1_relat_1(B_341) | ~v1_funct_1(A_343) | ~v1_relat_1(A_343))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.18/1.80  tff(c_2076, plain, (![B_341]: (k1_funct_1(B_341, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_341) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_341)) | ~v1_funct_1(B_341) | ~v1_relat_1(B_341) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1628, c_2070])).
% 4.18/1.80  tff(c_2083, plain, (![B_344]: (k1_funct_1(B_344, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_344) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_344)) | ~v1_funct_1(B_344) | ~v1_relat_1(B_344))), inference(demodulation, [status(thm), theory('equality')], [c_1596, c_42, c_2076])).
% 4.18/1.80  tff(c_2086, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1746, c_2083])).
% 4.18/1.80  tff(c_2088, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1593, c_38, c_1683, c_1572, c_2086])).
% 4.18/1.80  tff(c_2090, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1574, c_2088])).
% 4.18/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/1.80  
% 4.18/1.80  Inference rules
% 4.18/1.80  ----------------------
% 4.18/1.80  #Ref     : 2
% 4.18/1.80  #Sup     : 393
% 4.18/1.80  #Fact    : 0
% 4.18/1.80  #Define  : 0
% 4.18/1.80  #Split   : 13
% 4.18/1.80  #Chain   : 0
% 4.18/1.80  #Close   : 0
% 4.18/1.80  
% 4.18/1.80  Ordering : KBO
% 4.18/1.80  
% 4.18/1.80  Simplification rules
% 4.18/1.80  ----------------------
% 4.18/1.80  #Subsume      : 68
% 4.18/1.80  #Demod        : 326
% 4.18/1.80  #Tautology    : 122
% 4.18/1.80  #SimpNegUnit  : 48
% 4.18/1.80  #BackRed      : 18
% 4.18/1.80  
% 4.18/1.80  #Partial instantiations: 0
% 4.18/1.80  #Strategies tried      : 1
% 4.18/1.80  
% 4.18/1.80  Timing (in seconds)
% 4.18/1.80  ----------------------
% 4.18/1.80  Preprocessing        : 0.35
% 4.18/1.80  Parsing              : 0.18
% 4.18/1.80  CNF conversion       : 0.03
% 4.18/1.80  Main loop            : 0.61
% 4.18/1.80  Inferencing          : 0.23
% 4.18/1.80  Reduction            : 0.19
% 4.18/1.80  Demodulation         : 0.13
% 4.18/1.80  BG Simplification    : 0.03
% 4.18/1.80  Subsumption          : 0.10
% 4.18/1.80  Abstraction          : 0.04
% 4.18/1.80  MUC search           : 0.00
% 4.18/1.80  Cooper               : 0.00
% 4.18/1.80  Total                : 1.01
% 4.18/1.80  Index Insertion      : 0.00
% 4.18/1.80  Index Deletion       : 0.00
% 4.18/1.80  Index Matching       : 0.00
% 4.18/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
