%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1037+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:18 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 338 expanded)
%              Number of leaves         :   21 ( 118 expanded)
%              Depth                    :   10
%              Number of atoms          :  252 (1295 expanded)
%              Number of equality atoms :   42 ( 425 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( ( B = k1_xboole_0
             => A = k1_xboole_0 )
            & ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,A,B)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ~ r1_partfun1(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ~ ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
          & ! [D] :
              ( ( v1_funct_1(D)
                & v1_funct_2(D,A,B)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ? [E] :
                  ( r2_hidden(E,k1_relset_1(A,B,C))
                  & k1_funct_1(D,E) != k1_funct_1(C,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
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

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_37,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_48,plain,(
    ! [B_28,A_29,C_30] :
      ( k1_xboole_0 = B_28
      | v1_funct_1('#skF_1'(A_29,B_28,C_30))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_29,B_28)))
      | ~ v1_funct_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_51,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_1('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_48])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_1('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_51])).

tff(c_55,plain,(
    v1_funct_1('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_54])).

tff(c_68,plain,(
    ! [B_33,A_34,C_35] :
      ( k1_xboole_0 = B_33
      | v1_funct_2('#skF_1'(A_34,B_33,C_35),A_34,B_33)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_34,B_33)))
      | ~ v1_funct_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_72,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_68])).

tff(c_76,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_72])).

tff(c_77,plain,(
    v1_funct_2('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_76])).

tff(c_78,plain,(
    ! [B_36,A_37,C_38] :
      ( k1_xboole_0 = B_36
      | m1_subset_1('#skF_1'(A_37,B_36,C_38),k1_zfmisc_1(k2_zfmisc_1(A_37,B_36)))
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_37,B_36)))
      | ~ v1_funct_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,(
    ! [D_22] :
      ( ~ r1_partfun1('#skF_5',D_22)
      | ~ m1_subset_1(D_22,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2(D_22,'#skF_3','#skF_4')
      | ~ v1_funct_1(D_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_90,plain,(
    ! [C_38] :
      ( ~ r1_partfun1('#skF_5','#skF_1'('#skF_3','#skF_4',C_38))
      | ~ v1_funct_2('#skF_1'('#skF_3','#skF_4',C_38),'#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_1'('#skF_3','#skF_4',C_38))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_38) ) ),
    inference(resolution,[status(thm)],[c_78,c_30])).

tff(c_124,plain,(
    ! [C_47] :
      ( ~ r1_partfun1('#skF_5','#skF_1'('#skF_3','#skF_4',C_47))
      | ~ v1_funct_2('#skF_1'('#skF_3','#skF_4',C_47),'#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_1'('#skF_3','#skF_4',C_47))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_47) ) ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_90])).

tff(c_131,plain,
    ( ~ r1_partfun1('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_124])).

tff(c_137,plain,(
    ~ r1_partfun1('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_55,c_77,c_131])).

tff(c_8,plain,(
    ! [B_2,A_1,C_3] :
      ( k1_xboole_0 = B_2
      | m1_subset_1('#skF_1'(A_1,B_2,C_3),k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_163,plain,(
    ! [B_71,A_72,C_73,D_74] :
      ( k1_xboole_0 = B_71
      | r2_hidden('#skF_2'(A_72,B_71,C_73,D_74),k1_relset_1(A_72,B_71,C_73))
      | r1_partfun1(C_73,D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71)))
      | ~ v1_funct_2(D_74,A_72,B_71)
      | ~ v1_funct_1(D_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71)))
      | ~ v1_funct_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [B_2,A_1,C_3,E_8] :
      ( k1_xboole_0 = B_2
      | k1_funct_1('#skF_1'(A_1,B_2,C_3),E_8) = k1_funct_1(C_3,E_8)
      | ~ r2_hidden(E_8,k1_relset_1(A_1,B_2,C_3))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_236,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k1_funct_1('#skF_1'(A_105,B_106,C_107),'#skF_2'(A_105,B_106,C_107,D_108)) = k1_funct_1(C_107,'#skF_2'(A_105,B_106,C_107,D_108))
      | k1_xboole_0 = B_106
      | r1_partfun1(C_107,D_108)
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ v1_funct_2(D_108,A_105,B_106)
      | ~ v1_funct_1(D_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ v1_funct_1(C_107) ) ),
    inference(resolution,[status(thm)],[c_163,c_4])).

tff(c_304,plain,(
    ! [A_127,B_128,C_129,C_130] :
      ( k1_funct_1('#skF_1'(A_127,B_128,C_129),'#skF_2'(A_127,B_128,C_129,'#skF_1'(A_127,B_128,C_130))) = k1_funct_1(C_129,'#skF_2'(A_127,B_128,C_129,'#skF_1'(A_127,B_128,C_130)))
      | r1_partfun1(C_129,'#skF_1'(A_127,B_128,C_130))
      | ~ v1_funct_2('#skF_1'(A_127,B_128,C_130),A_127,B_128)
      | ~ v1_funct_1('#skF_1'(A_127,B_128,C_130))
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ v1_funct_1(C_129)
      | k1_xboole_0 = B_128
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ v1_funct_1(C_130) ) ),
    inference(resolution,[status(thm)],[c_8,c_236])).

tff(c_20,plain,(
    ! [B_10,D_17,A_9,C_11] :
      ( k1_xboole_0 = B_10
      | k1_funct_1(D_17,'#skF_2'(A_9,B_10,C_11,D_17)) != k1_funct_1(C_11,'#skF_2'(A_9,B_10,C_11,D_17))
      | r1_partfun1(C_11,D_17)
      | ~ m1_subset_1(D_17,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_2(D_17,A_9,B_10)
      | ~ v1_funct_1(D_17)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_330,plain,(
    ! [A_131,B_132,C_133] :
      ( ~ m1_subset_1('#skF_1'(A_131,B_132,C_133),k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | r1_partfun1(C_133,'#skF_1'(A_131,B_132,C_133))
      | ~ v1_funct_2('#skF_1'(A_131,B_132,C_133),A_131,B_132)
      | ~ v1_funct_1('#skF_1'(A_131,B_132,C_133))
      | k1_xboole_0 = B_132
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_1(C_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_20])).

tff(c_337,plain,(
    ! [C_134,A_135,B_136] :
      ( r1_partfun1(C_134,'#skF_1'(A_135,B_136,C_134))
      | ~ v1_funct_2('#skF_1'(A_135,B_136,C_134),A_135,B_136)
      | ~ v1_funct_1('#skF_1'(A_135,B_136,C_134))
      | k1_xboole_0 = B_136
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | ~ v1_funct_1(C_134) ) ),
    inference(resolution,[status(thm)],[c_8,c_330])).

tff(c_343,plain,
    ( r1_partfun1('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_77,c_337])).

tff(c_348,plain,
    ( r1_partfun1('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_55,c_343])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_137,c_348])).

tff(c_352,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_351,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_357,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_351])).

tff(c_362,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_34])).

tff(c_14,plain,(
    ! [B_2,C_3] :
      ( v1_funct_1('#skF_1'(k1_xboole_0,B_2,C_3))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_368,plain,(
    ! [B_137,C_138] :
      ( v1_funct_1('#skF_1'('#skF_4',B_137,C_138))
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_137)))
      | ~ v1_funct_1(C_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_352,c_14])).

tff(c_371,plain,
    ( v1_funct_1('#skF_1'('#skF_4','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_362,c_368])).

tff(c_374,plain,(
    v1_funct_1('#skF_1'('#skF_4','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_371])).

tff(c_10,plain,(
    ! [B_2,C_3] :
      ( v1_funct_2('#skF_1'(k1_xboole_0,B_2,C_3),k1_xboole_0,B_2)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_385,plain,(
    ! [B_142,C_143] :
      ( v1_funct_2('#skF_1'('#skF_4',B_142,C_143),'#skF_4',B_142)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_142)))
      | ~ v1_funct_1(C_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_352,c_352,c_10])).

tff(c_387,plain,
    ( v1_funct_2('#skF_1'('#skF_4','#skF_4','#skF_5'),'#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_362,c_385])).

tff(c_390,plain,(
    v1_funct_2('#skF_1'('#skF_4','#skF_4','#skF_5'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_387])).

tff(c_6,plain,(
    ! [B_2,C_3] :
      ( m1_subset_1('#skF_1'(k1_xboole_0,B_2,C_3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_401,plain,(
    ! [B_145,C_146] :
      ( m1_subset_1('#skF_1'('#skF_4',B_145,C_146),k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_145)))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_145)))
      | ~ v1_funct_1(C_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_352,c_352,c_6])).

tff(c_391,plain,(
    ! [D_22] :
      ( ~ r1_partfun1('#skF_5',D_22)
      | ~ m1_subset_1(D_22,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_2(D_22,'#skF_4','#skF_4')
      | ~ v1_funct_1(D_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_357,c_30])).

tff(c_469,plain,(
    ! [C_160] :
      ( ~ r1_partfun1('#skF_5','#skF_1'('#skF_4','#skF_4',C_160))
      | ~ v1_funct_2('#skF_1'('#skF_4','#skF_4',C_160),'#skF_4','#skF_4')
      | ~ v1_funct_1('#skF_1'('#skF_4','#skF_4',C_160))
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_1(C_160) ) ),
    inference(resolution,[status(thm)],[c_401,c_391])).

tff(c_480,plain,
    ( ~ r1_partfun1('#skF_5','#skF_1'('#skF_4','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_1'('#skF_4','#skF_4','#skF_5'),'#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_1'('#skF_4','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_362,c_469])).

tff(c_486,plain,(
    ~ r1_partfun1('#skF_5','#skF_1'('#skF_4','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_374,c_390,c_480])).

tff(c_400,plain,(
    ! [B_2,C_3] :
      ( m1_subset_1('#skF_1'('#skF_4',B_2,C_3),k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_2)))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_352,c_352,c_6])).

tff(c_22,plain,(
    ! [B_10,C_11,D_17] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_10,C_11,D_17),k1_relset_1(k1_xboole_0,B_10,C_11))
      | r1_partfun1(C_11,D_17)
      | ~ m1_subset_1(D_17,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_10)))
      | ~ v1_funct_2(D_17,k1_xboole_0,B_10)
      | ~ v1_funct_1(D_17)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_10)))
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_504,plain,(
    ! [B_171,C_172,D_173] :
      ( r2_hidden('#skF_2'('#skF_4',B_171,C_172,D_173),k1_relset_1('#skF_4',B_171,C_172))
      | r1_partfun1(C_172,D_173)
      | ~ m1_subset_1(D_173,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_171)))
      | ~ v1_funct_2(D_173,'#skF_4',B_171)
      | ~ v1_funct_1(D_173)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_171)))
      | ~ v1_funct_1(C_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_352,c_352,c_352,c_352,c_22])).

tff(c_2,plain,(
    ! [B_2,C_3,E_8] :
      ( k1_funct_1('#skF_1'(k1_xboole_0,B_2,C_3),E_8) = k1_funct_1(C_3,E_8)
      | ~ r2_hidden(E_8,k1_relset_1(k1_xboole_0,B_2,C_3))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_466,plain,(
    ! [B_2,C_3,E_8] :
      ( k1_funct_1('#skF_1'('#skF_4',B_2,C_3),E_8) = k1_funct_1(C_3,E_8)
      | ~ r2_hidden(E_8,k1_relset_1('#skF_4',B_2,C_3))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_352,c_352,c_2])).

tff(c_596,plain,(
    ! [B_210,C_211,D_212] :
      ( k1_funct_1('#skF_1'('#skF_4',B_210,C_211),'#skF_2'('#skF_4',B_210,C_211,D_212)) = k1_funct_1(C_211,'#skF_2'('#skF_4',B_210,C_211,D_212))
      | r1_partfun1(C_211,D_212)
      | ~ m1_subset_1(D_212,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_210)))
      | ~ v1_funct_2(D_212,'#skF_4',B_210)
      | ~ v1_funct_1(D_212)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_210)))
      | ~ v1_funct_1(C_211) ) ),
    inference(resolution,[status(thm)],[c_504,c_466])).

tff(c_654,plain,(
    ! [B_232,C_233,C_234] :
      ( k1_funct_1('#skF_1'('#skF_4',B_232,C_233),'#skF_2'('#skF_4',B_232,C_233,'#skF_1'('#skF_4',B_232,C_234))) = k1_funct_1(C_233,'#skF_2'('#skF_4',B_232,C_233,'#skF_1'('#skF_4',B_232,C_234)))
      | r1_partfun1(C_233,'#skF_1'('#skF_4',B_232,C_234))
      | ~ v1_funct_2('#skF_1'('#skF_4',B_232,C_234),'#skF_4',B_232)
      | ~ v1_funct_1('#skF_1'('#skF_4',B_232,C_234))
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_232)))
      | ~ v1_funct_1(C_233)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_232)))
      | ~ v1_funct_1(C_234) ) ),
    inference(resolution,[status(thm)],[c_400,c_596])).

tff(c_18,plain,(
    ! [D_17,B_10,C_11] :
      ( k1_funct_1(D_17,'#skF_2'(k1_xboole_0,B_10,C_11,D_17)) != k1_funct_1(C_11,'#skF_2'(k1_xboole_0,B_10,C_11,D_17))
      | r1_partfun1(C_11,D_17)
      | ~ m1_subset_1(D_17,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_10)))
      | ~ v1_funct_2(D_17,k1_xboole_0,B_10)
      | ~ v1_funct_1(D_17)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_10)))
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_552,plain,(
    ! [D_17,B_10,C_11] :
      ( k1_funct_1(D_17,'#skF_2'('#skF_4',B_10,C_11,D_17)) != k1_funct_1(C_11,'#skF_2'('#skF_4',B_10,C_11,D_17))
      | r1_partfun1(C_11,D_17)
      | ~ m1_subset_1(D_17,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_10)))
      | ~ v1_funct_2(D_17,'#skF_4',B_10)
      | ~ v1_funct_1(D_17)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_10)))
      | ~ v1_funct_1(C_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_352,c_352,c_352,c_352,c_18])).

tff(c_671,plain,(
    ! [B_235,C_236] :
      ( ~ m1_subset_1('#skF_1'('#skF_4',B_235,C_236),k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_235)))
      | r1_partfun1(C_236,'#skF_1'('#skF_4',B_235,C_236))
      | ~ v1_funct_2('#skF_1'('#skF_4',B_235,C_236),'#skF_4',B_235)
      | ~ v1_funct_1('#skF_1'('#skF_4',B_235,C_236))
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_235)))
      | ~ v1_funct_1(C_236) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_552])).

tff(c_679,plain,(
    ! [C_237,B_238] :
      ( r1_partfun1(C_237,'#skF_1'('#skF_4',B_238,C_237))
      | ~ v1_funct_2('#skF_1'('#skF_4',B_238,C_237),'#skF_4',B_238)
      | ~ v1_funct_1('#skF_1'('#skF_4',B_238,C_237))
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_238)))
      | ~ v1_funct_1(C_237) ) ),
    inference(resolution,[status(thm)],[c_400,c_671])).

tff(c_686,plain,
    ( r1_partfun1('#skF_5','#skF_1'('#skF_4','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_1'('#skF_4','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_390,c_679])).

tff(c_691,plain,(
    r1_partfun1('#skF_5','#skF_1'('#skF_4','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_362,c_374,c_686])).

tff(c_693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_486,c_691])).

%------------------------------------------------------------------------------
