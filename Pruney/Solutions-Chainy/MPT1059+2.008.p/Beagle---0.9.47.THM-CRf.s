%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:34 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 127 expanded)
%              Number of leaves         :   38 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  154 ( 325 expanded)
%              Number of equality atoms :   41 (  75 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

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
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_86,axiom,(
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

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_44,plain,(
    m1_subset_1('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_137,plain,(
    ! [C_72,B_73,A_74] :
      ( v5_relat_1(C_72,B_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_146,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_137])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_92,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_101,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_92])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_74,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_82,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_74])).

tff(c_102,plain,(
    ! [A_62,C_63,B_64] :
      ( r1_tarski(A_62,C_63)
      | ~ r1_tarski(B_64,C_63)
      | ~ r1_tarski(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_107,plain,(
    ! [A_62] :
      ( r1_tarski(A_62,k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_62,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_82,c_102])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_313,plain,(
    ! [B_115,C_116,A_117] :
      ( k1_xboole_0 = B_115
      | v1_funct_2(C_116,A_117,B_115)
      | k1_relset_1(A_117,B_115,C_116) != A_117
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_339,plain,(
    ! [B_121,A_122,A_123] :
      ( k1_xboole_0 = B_121
      | v1_funct_2(A_122,A_123,B_121)
      | k1_relset_1(A_123,B_121,A_122) != A_123
      | ~ r1_tarski(A_122,k2_zfmisc_1(A_123,B_121)) ) ),
    inference(resolution,[status(thm)],[c_14,c_313])).

tff(c_350,plain,(
    ! [A_62] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(A_62,'#skF_2','#skF_3')
      | k1_relset_1('#skF_2','#skF_3',A_62) != '#skF_2'
      | ~ r1_tarski(A_62,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_107,c_339])).

tff(c_355,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_8,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    ! [A_51] :
      ( v1_xboole_0(A_51)
      | r2_hidden('#skF_1'(A_51),A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_67,plain,(
    ! [A_52] :
      ( ~ r1_tarski(A_52,'#skF_1'(A_52))
      | v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_58,c_16])).

tff(c_72,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_67])).

tff(c_372,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_72])).

tff(c_375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_372])).

tff(c_377,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_193,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_202,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_193])).

tff(c_386,plain,(
    ! [B_127,A_128,C_129] :
      ( k1_xboole_0 = B_127
      | k1_relset_1(A_128,B_127,C_129) = A_128
      | ~ v1_funct_2(C_129,A_128,B_127)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_393,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_386])).

tff(c_397,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_202,c_393])).

tff(c_398,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_377,c_397])).

tff(c_38,plain,(
    ! [A_27,B_28,C_30] :
      ( k7_partfun1(A_27,B_28,C_30) = k1_funct_1(B_28,C_30)
      | ~ r2_hidden(C_30,k1_relat_1(B_28))
      | ~ v1_funct_1(B_28)
      | ~ v5_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_411,plain,(
    ! [A_27,C_30] :
      ( k7_partfun1(A_27,'#skF_4',C_30) = k1_funct_1('#skF_4',C_30)
      | ~ r2_hidden(C_30,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_27)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_38])).

tff(c_421,plain,(
    ! [A_133,C_134] :
      ( k7_partfun1(A_133,'#skF_4',C_134) = k1_funct_1('#skF_4',C_134)
      | ~ r2_hidden(C_134,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_50,c_411])).

tff(c_424,plain,(
    ! [A_133,A_9] :
      ( k7_partfun1(A_133,'#skF_4',A_9) = k1_funct_1('#skF_4',A_9)
      | ~ v5_relat_1('#skF_4',A_133)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_9,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_10,c_421])).

tff(c_443,plain,(
    ! [A_136,A_137] :
      ( k7_partfun1(A_136,'#skF_4',A_137) = k1_funct_1('#skF_4',A_137)
      | ~ v5_relat_1('#skF_4',A_136)
      | ~ m1_subset_1(A_137,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_424])).

tff(c_451,plain,(
    ! [A_138] :
      ( k7_partfun1('#skF_3','#skF_4',A_138) = k1_funct_1('#skF_4',A_138)
      | ~ m1_subset_1(A_138,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_146,c_443])).

tff(c_455,plain,(
    k7_partfun1('#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_451])).

tff(c_42,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') != k7_partfun1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_456,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') != k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_42])).

tff(c_461,plain,(
    ! [A_139,B_140,C_141,D_142] :
      ( k3_funct_2(A_139,B_140,C_141,D_142) = k1_funct_1(C_141,D_142)
      | ~ m1_subset_1(D_142,A_139)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ v1_funct_2(C_141,A_139,B_140)
      | ~ v1_funct_1(C_141)
      | v1_xboole_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_467,plain,(
    ! [B_140,C_141] :
      ( k3_funct_2('#skF_2',B_140,C_141,'#skF_5') = k1_funct_1(C_141,'#skF_5')
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_140)))
      | ~ v1_funct_2(C_141,'#skF_2',B_140)
      | ~ v1_funct_1(C_141)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_461])).

tff(c_529,plain,(
    ! [B_149,C_150] :
      ( k3_funct_2('#skF_2',B_149,C_150,'#skF_5') = k1_funct_1(C_150,'#skF_5')
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_149)))
      | ~ v1_funct_2(C_150,'#skF_2',B_149)
      | ~ v1_funct_1(C_150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_467])).

tff(c_536,plain,
    ( k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_529])).

tff(c_540,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_536])).

tff(c_542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_456,c_540])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:47:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.36  
% 2.76/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.36  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.76/1.36  
% 2.76/1.36  %Foreground sorts:
% 2.76/1.36  
% 2.76/1.36  
% 2.76/1.36  %Background operators:
% 2.76/1.36  
% 2.76/1.36  
% 2.76/1.36  %Foreground operators:
% 2.76/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.76/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.76/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.36  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.76/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.76/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.76/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.76/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.76/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.76/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.76/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.76/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.36  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.76/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.76/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.36  
% 2.85/1.38  tff(f_130, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_2)).
% 2.85/1.38  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.85/1.38  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.85/1.38  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.85/1.38  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.85/1.38  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.85/1.38  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.85/1.38  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.85/1.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.85/1.38  tff(f_54, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.85/1.38  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.85/1.38  tff(f_97, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 2.85/1.38  tff(f_110, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.85/1.38  tff(c_44, plain, (m1_subset_1('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.85/1.38  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.85/1.38  tff(c_137, plain, (![C_72, B_73, A_74]: (v5_relat_1(C_72, B_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.85/1.38  tff(c_146, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_137])).
% 2.85/1.38  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.85/1.38  tff(c_10, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | v1_xboole_0(B_10) | ~m1_subset_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.85/1.38  tff(c_92, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.85/1.38  tff(c_101, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_92])).
% 2.85/1.38  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.85/1.38  tff(c_52, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.85/1.38  tff(c_74, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.85/1.38  tff(c_82, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_74])).
% 2.85/1.38  tff(c_102, plain, (![A_62, C_63, B_64]: (r1_tarski(A_62, C_63) | ~r1_tarski(B_64, C_63) | ~r1_tarski(A_62, B_64))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.85/1.38  tff(c_107, plain, (![A_62]: (r1_tarski(A_62, k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski(A_62, '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_102])).
% 2.85/1.38  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.85/1.38  tff(c_313, plain, (![B_115, C_116, A_117]: (k1_xboole_0=B_115 | v1_funct_2(C_116, A_117, B_115) | k1_relset_1(A_117, B_115, C_116)!=A_117 | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_115))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.85/1.38  tff(c_339, plain, (![B_121, A_122, A_123]: (k1_xboole_0=B_121 | v1_funct_2(A_122, A_123, B_121) | k1_relset_1(A_123, B_121, A_122)!=A_123 | ~r1_tarski(A_122, k2_zfmisc_1(A_123, B_121)))), inference(resolution, [status(thm)], [c_14, c_313])).
% 2.85/1.38  tff(c_350, plain, (![A_62]: (k1_xboole_0='#skF_3' | v1_funct_2(A_62, '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', A_62)!='#skF_2' | ~r1_tarski(A_62, '#skF_4'))), inference(resolution, [status(thm)], [c_107, c_339])).
% 2.85/1.38  tff(c_355, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_350])).
% 2.85/1.38  tff(c_8, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.85/1.38  tff(c_58, plain, (![A_51]: (v1_xboole_0(A_51) | r2_hidden('#skF_1'(A_51), A_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.85/1.38  tff(c_16, plain, (![B_14, A_13]: (~r1_tarski(B_14, A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.85/1.38  tff(c_67, plain, (![A_52]: (~r1_tarski(A_52, '#skF_1'(A_52)) | v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_58, c_16])).
% 2.85/1.38  tff(c_72, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_67])).
% 2.85/1.38  tff(c_372, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_355, c_72])).
% 2.85/1.38  tff(c_375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_372])).
% 2.85/1.38  tff(c_377, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_350])).
% 2.85/1.38  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.85/1.38  tff(c_193, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.85/1.38  tff(c_202, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_193])).
% 2.85/1.38  tff(c_386, plain, (![B_127, A_128, C_129]: (k1_xboole_0=B_127 | k1_relset_1(A_128, B_127, C_129)=A_128 | ~v1_funct_2(C_129, A_128, B_127) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.85/1.38  tff(c_393, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_386])).
% 2.85/1.38  tff(c_397, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_202, c_393])).
% 2.85/1.38  tff(c_398, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_377, c_397])).
% 2.85/1.38  tff(c_38, plain, (![A_27, B_28, C_30]: (k7_partfun1(A_27, B_28, C_30)=k1_funct_1(B_28, C_30) | ~r2_hidden(C_30, k1_relat_1(B_28)) | ~v1_funct_1(B_28) | ~v5_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.85/1.38  tff(c_411, plain, (![A_27, C_30]: (k7_partfun1(A_27, '#skF_4', C_30)=k1_funct_1('#skF_4', C_30) | ~r2_hidden(C_30, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_27) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_398, c_38])).
% 2.85/1.38  tff(c_421, plain, (![A_133, C_134]: (k7_partfun1(A_133, '#skF_4', C_134)=k1_funct_1('#skF_4', C_134) | ~r2_hidden(C_134, '#skF_2') | ~v5_relat_1('#skF_4', A_133))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_50, c_411])).
% 2.85/1.38  tff(c_424, plain, (![A_133, A_9]: (k7_partfun1(A_133, '#skF_4', A_9)=k1_funct_1('#skF_4', A_9) | ~v5_relat_1('#skF_4', A_133) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_9, '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_421])).
% 2.85/1.38  tff(c_443, plain, (![A_136, A_137]: (k7_partfun1(A_136, '#skF_4', A_137)=k1_funct_1('#skF_4', A_137) | ~v5_relat_1('#skF_4', A_136) | ~m1_subset_1(A_137, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_424])).
% 2.85/1.38  tff(c_451, plain, (![A_138]: (k7_partfun1('#skF_3', '#skF_4', A_138)=k1_funct_1('#skF_4', A_138) | ~m1_subset_1(A_138, '#skF_2'))), inference(resolution, [status(thm)], [c_146, c_443])).
% 2.85/1.38  tff(c_455, plain, (k7_partfun1('#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_451])).
% 2.85/1.38  tff(c_42, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k7_partfun1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.85/1.38  tff(c_456, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_455, c_42])).
% 2.85/1.38  tff(c_461, plain, (![A_139, B_140, C_141, D_142]: (k3_funct_2(A_139, B_140, C_141, D_142)=k1_funct_1(C_141, D_142) | ~m1_subset_1(D_142, A_139) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))) | ~v1_funct_2(C_141, A_139, B_140) | ~v1_funct_1(C_141) | v1_xboole_0(A_139))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.85/1.38  tff(c_467, plain, (![B_140, C_141]: (k3_funct_2('#skF_2', B_140, C_141, '#skF_5')=k1_funct_1(C_141, '#skF_5') | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_140))) | ~v1_funct_2(C_141, '#skF_2', B_140) | ~v1_funct_1(C_141) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_461])).
% 2.85/1.38  tff(c_529, plain, (![B_149, C_150]: (k3_funct_2('#skF_2', B_149, C_150, '#skF_5')=k1_funct_1(C_150, '#skF_5') | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_149))) | ~v1_funct_2(C_150, '#skF_2', B_149) | ~v1_funct_1(C_150))), inference(negUnitSimplification, [status(thm)], [c_54, c_467])).
% 2.85/1.38  tff(c_536, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_529])).
% 2.85/1.38  tff(c_540, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_536])).
% 2.85/1.38  tff(c_542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_456, c_540])).
% 2.85/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.38  
% 2.85/1.38  Inference rules
% 2.85/1.38  ----------------------
% 2.85/1.38  #Ref     : 0
% 2.85/1.38  #Sup     : 90
% 2.85/1.38  #Fact    : 0
% 2.85/1.38  #Define  : 0
% 2.85/1.38  #Split   : 3
% 2.85/1.38  #Chain   : 0
% 2.85/1.38  #Close   : 0
% 2.85/1.38  
% 2.85/1.38  Ordering : KBO
% 2.85/1.38  
% 2.85/1.38  Simplification rules
% 2.85/1.38  ----------------------
% 2.85/1.38  #Subsume      : 4
% 2.85/1.38  #Demod        : 75
% 2.85/1.38  #Tautology    : 36
% 2.85/1.38  #SimpNegUnit  : 11
% 2.85/1.38  #BackRed      : 20
% 2.85/1.38  
% 2.85/1.38  #Partial instantiations: 0
% 2.85/1.38  #Strategies tried      : 1
% 2.85/1.38  
% 2.85/1.38  Timing (in seconds)
% 2.85/1.38  ----------------------
% 2.85/1.38  Preprocessing        : 0.33
% 2.85/1.38  Parsing              : 0.17
% 2.85/1.38  CNF conversion       : 0.02
% 2.85/1.38  Main loop            : 0.29
% 2.85/1.38  Inferencing          : 0.11
% 2.85/1.38  Reduction            : 0.09
% 2.85/1.38  Demodulation         : 0.06
% 2.85/1.38  BG Simplification    : 0.02
% 2.85/1.38  Subsumption          : 0.06
% 2.85/1.38  Abstraction          : 0.01
% 2.85/1.38  MUC search           : 0.00
% 2.85/1.38  Cooper               : 0.00
% 2.85/1.38  Total                : 0.66
% 2.85/1.38  Index Insertion      : 0.00
% 2.85/1.38  Index Deletion       : 0.00
% 2.85/1.38  Index Matching       : 0.00
% 2.85/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
