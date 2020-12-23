%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:00 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 394 expanded)
%              Number of leaves         :   20 ( 145 expanded)
%              Depth                    :   15
%              Number of atoms          :  214 (1806 expanded)
%              Number of equality atoms :   46 ( 353 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r1_partfun1(B,C)
            <=> ! [D] :
                  ( r2_hidden(D,k1_relset_1(A,A,B))
                 => k1_funct_1(B,D) = k1_funct_1(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_2)).

tff(f_47,axiom,(
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

tff(c_24,plain,
    ( k1_funct_1('#skF_3','#skF_5') != k1_funct_1('#skF_4','#skF_5')
    | ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_35,plain,(
    ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_43,plain,(
    ! [B_29,A_30,C_31,D_32] :
      ( k1_xboole_0 = B_29
      | r2_hidden('#skF_1'(A_30,B_29,C_31,D_32),k1_relset_1(A_30,B_29,C_31))
      | r1_partfun1(C_31,D_32)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_29)))
      | ~ v1_funct_2(D_32,A_30,B_29)
      | ~ v1_funct_1(D_32)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_30,B_29)))
      | ~ v1_funct_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    ! [D_20] :
      ( r1_partfun1('#skF_3','#skF_4')
      | k1_funct_1('#skF_3',D_20) = k1_funct_1('#skF_4',D_20)
      | ~ r2_hidden(D_20,k1_relset_1('#skF_2','#skF_2','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36,plain,(
    ! [D_20] :
      ( k1_funct_1('#skF_3',D_20) = k1_funct_1('#skF_4',D_20)
      | ~ r2_hidden(D_20,k1_relset_1('#skF_2','#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_34])).

tff(c_50,plain,(
    ! [D_32] :
      ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_2','#skF_3',D_32)) = k1_funct_1('#skF_4','#skF_1'('#skF_2','#skF_2','#skF_3',D_32))
      | k1_xboole_0 = '#skF_2'
      | r1_partfun1('#skF_3',D_32)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(D_32,'#skF_2','#skF_2')
      | ~ v1_funct_1(D_32)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_43,c_36])).

tff(c_54,plain,(
    ! [D_32] :
      ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_2','#skF_3',D_32)) = k1_funct_1('#skF_4','#skF_1'('#skF_2','#skF_2','#skF_3',D_32))
      | k1_xboole_0 = '#skF_2'
      | r1_partfun1('#skF_3',D_32)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(D_32,'#skF_2','#skF_2')
      | ~ v1_funct_1(D_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_50])).

tff(c_55,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_6,plain,(
    ! [B_2,C_3,D_9] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_2,C_3,D_9),k1_relset_1(k1_xboole_0,B_2,C_3))
      | r1_partfun1(C_3,D_9)
      | ~ m1_subset_1(D_9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_2(D_9,k1_xboole_0,B_2)
      | ~ v1_funct_1(D_9)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_81,plain,(
    ! [B_38,C_39,D_40] :
      ( r2_hidden('#skF_1'('#skF_2',B_38,C_39,D_40),k1_relset_1('#skF_2',B_38,C_39))
      | r1_partfun1(C_39,D_40)
      | ~ m1_subset_1(D_40,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_38)))
      | ~ v1_funct_2(D_40,'#skF_2',B_38)
      | ~ v1_funct_1(D_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_38)))
      | ~ v1_funct_1(C_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_55,c_55,c_55,c_6])).

tff(c_85,plain,(
    ! [D_40] :
      ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_2','#skF_3',D_40)) = k1_funct_1('#skF_4','#skF_1'('#skF_2','#skF_2','#skF_3',D_40))
      | r1_partfun1('#skF_3',D_40)
      | ~ m1_subset_1(D_40,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(D_40,'#skF_2','#skF_2')
      | ~ v1_funct_1(D_40)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_81,c_36])).

tff(c_89,plain,(
    ! [D_41] :
      ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_2','#skF_3',D_41)) = k1_funct_1('#skF_4','#skF_1'('#skF_2','#skF_2','#skF_3',D_41))
      | r1_partfun1('#skF_3',D_41)
      | ~ m1_subset_1(D_41,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(D_41,'#skF_2','#skF_2')
      | ~ v1_funct_1(D_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_85])).

tff(c_95,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_2','#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_2','#skF_2','#skF_3','#skF_4'))
    | r1_partfun1('#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_89])).

tff(c_101,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_2','#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_2','#skF_2','#skF_3','#skF_4'))
    | r1_partfun1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_95])).

tff(c_102,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_2','#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_2','#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_101])).

tff(c_2,plain,(
    ! [D_9,B_2,C_3] :
      ( k1_funct_1(D_9,'#skF_1'(k1_xboole_0,B_2,C_3,D_9)) != k1_funct_1(C_3,'#skF_1'(k1_xboole_0,B_2,C_3,D_9))
      | r1_partfun1(C_3,D_9)
      | ~ m1_subset_1(D_9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_2(D_9,k1_xboole_0,B_2)
      | ~ v1_funct_1(D_9)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_134,plain,(
    ! [D_55,B_56,C_57] :
      ( k1_funct_1(D_55,'#skF_1'('#skF_2',B_56,C_57,D_55)) != k1_funct_1(C_57,'#skF_1'('#skF_2',B_56,C_57,D_55))
      | r1_partfun1(C_57,D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_56)))
      | ~ v1_funct_2(D_55,'#skF_2',B_56)
      | ~ v1_funct_1(D_55)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_56)))
      | ~ v1_funct_1(C_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_55,c_55,c_55,c_2])).

tff(c_136,plain,
    ( r1_partfun1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_134])).

tff(c_139,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_16,c_14,c_136])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_139])).

tff(c_143,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_144,plain,(
    ! [D_58] :
      ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_2','#skF_3',D_58)) = k1_funct_1('#skF_4','#skF_1'('#skF_2','#skF_2','#skF_3',D_58))
      | r1_partfun1('#skF_3',D_58)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(D_58,'#skF_2','#skF_2')
      | ~ v1_funct_1(D_58) ) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_150,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_2','#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_2','#skF_2','#skF_3','#skF_4'))
    | r1_partfun1('#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_144])).

tff(c_156,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_2','#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_2','#skF_2','#skF_3','#skF_4'))
    | r1_partfun1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_150])).

tff(c_157,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_2','#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_2','#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_156])).

tff(c_177,plain,(
    ! [B_67,D_68,A_69,C_70] :
      ( k1_xboole_0 = B_67
      | k1_funct_1(D_68,'#skF_1'(A_69,B_67,C_70,D_68)) != k1_funct_1(C_70,'#skF_1'(A_69,B_67,C_70,D_68))
      | r1_partfun1(C_70,D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_67)))
      | ~ v1_funct_2(D_68,A_69,B_67)
      | ~ v1_funct_1(D_68)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_69,B_67)))
      | ~ v1_funct_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_179,plain,
    ( k1_xboole_0 = '#skF_2'
    | r1_partfun1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_177])).

tff(c_182,plain,
    ( k1_xboole_0 = '#skF_2'
    | r1_partfun1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_16,c_14,c_179])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_143,c_182])).

tff(c_185,plain,(
    k1_funct_1('#skF_3','#skF_5') != k1_funct_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_186,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_26,plain,
    ( r2_hidden('#skF_5',k1_relset_1('#skF_2','#skF_2','#skF_3'))
    | ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_188,plain,(
    r2_hidden('#skF_5',k1_relset_1('#skF_2','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_26])).

tff(c_206,plain,(
    ! [E_88,B_89,C_90,A_91,D_87] :
      ( k1_xboole_0 = B_89
      | k1_funct_1(D_87,E_88) = k1_funct_1(C_90,E_88)
      | ~ r2_hidden(E_88,k1_relset_1(A_91,B_89,C_90))
      | ~ r1_partfun1(C_90,D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1(A_91,B_89)))
      | ~ v1_funct_2(D_87,A_91,B_89)
      | ~ v1_funct_1(D_87)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_89)))
      | ~ v1_funct_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_212,plain,(
    ! [D_87] :
      ( k1_xboole_0 = '#skF_2'
      | k1_funct_1(D_87,'#skF_5') = k1_funct_1('#skF_3','#skF_5')
      | ~ r1_partfun1('#skF_3',D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(D_87,'#skF_2','#skF_2')
      | ~ v1_funct_1(D_87)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_188,c_206])).

tff(c_217,plain,(
    ! [D_87] :
      ( k1_xboole_0 = '#skF_2'
      | k1_funct_1(D_87,'#skF_5') = k1_funct_1('#skF_3','#skF_5')
      | ~ r1_partfun1('#skF_3',D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(D_87,'#skF_2','#skF_2')
      | ~ v1_funct_1(D_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_212])).

tff(c_218,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_10,plain,(
    ! [D_9,E_12,C_3,B_2] :
      ( k1_funct_1(D_9,E_12) = k1_funct_1(C_3,E_12)
      | ~ r2_hidden(E_12,k1_relset_1(k1_xboole_0,B_2,C_3))
      | ~ r1_partfun1(C_3,D_9)
      | ~ m1_subset_1(D_9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_2(D_9,k1_xboole_0,B_2)
      | ~ v1_funct_1(D_9)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_259,plain,(
    ! [D_104,E_105,C_106,B_107] :
      ( k1_funct_1(D_104,E_105) = k1_funct_1(C_106,E_105)
      | ~ r2_hidden(E_105,k1_relset_1('#skF_2',B_107,C_106))
      | ~ r1_partfun1(C_106,D_104)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_107)))
      | ~ v1_funct_2(D_104,'#skF_2',B_107)
      | ~ v1_funct_1(D_104)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_107)))
      | ~ v1_funct_1(C_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_218,c_218,c_218,c_10])).

tff(c_263,plain,(
    ! [D_104] :
      ( k1_funct_1(D_104,'#skF_5') = k1_funct_1('#skF_3','#skF_5')
      | ~ r1_partfun1('#skF_3',D_104)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(D_104,'#skF_2','#skF_2')
      | ~ v1_funct_1(D_104)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_188,c_259])).

tff(c_268,plain,(
    ! [D_108] :
      ( k1_funct_1(D_108,'#skF_5') = k1_funct_1('#skF_3','#skF_5')
      | ~ r1_partfun1('#skF_3',D_108)
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(D_108,'#skF_2','#skF_2')
      | ~ v1_funct_1(D_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_263])).

tff(c_274,plain,
    ( k1_funct_1('#skF_3','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ r1_partfun1('#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_268])).

tff(c_280,plain,(
    k1_funct_1('#skF_3','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_186,c_274])).

tff(c_282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_280])).

tff(c_285,plain,(
    ! [D_109] :
      ( k1_funct_1(D_109,'#skF_5') = k1_funct_1('#skF_3','#skF_5')
      | ~ r1_partfun1('#skF_3',D_109)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(D_109,'#skF_2','#skF_2')
      | ~ v1_funct_1(D_109) ) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_291,plain,
    ( k1_funct_1('#skF_3','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ r1_partfun1('#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_285])).

tff(c_298,plain,(
    k1_funct_1('#skF_3','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_186,c_291])).

tff(c_300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.38  
% 2.34/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.38  %$ v1_funct_2 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.34/1.38  
% 2.34/1.38  %Foreground sorts:
% 2.34/1.38  
% 2.34/1.38  
% 2.34/1.38  %Background operators:
% 2.34/1.38  
% 2.34/1.38  
% 2.34/1.38  %Foreground operators:
% 2.34/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.34/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.34/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.34/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.34/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.34/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.34/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.34/1.38  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.34/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.38  
% 2.56/1.40  tff(f_66, negated_conjecture, ~(![A, B]: ((v1_funct_1(B) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) <=> (![D]: (r2_hidden(D, k1_relset_1(A, A, B)) => (k1_funct_1(B, D) = k1_funct_1(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_2)).
% 2.56/1.40  tff(f_47, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (r1_partfun1(C, D) <=> (![E]: (r2_hidden(E, k1_relset_1(A, B, C)) => (k1_funct_1(C, E) = k1_funct_1(D, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_2)).
% 2.56/1.40  tff(c_24, plain, (k1_funct_1('#skF_3', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5') | ~r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.40  tff(c_35, plain, (~r1_partfun1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_24])).
% 2.56/1.40  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.40  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.40  tff(c_18, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.40  tff(c_16, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.40  tff(c_14, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.40  tff(c_43, plain, (![B_29, A_30, C_31, D_32]: (k1_xboole_0=B_29 | r2_hidden('#skF_1'(A_30, B_29, C_31, D_32), k1_relset_1(A_30, B_29, C_31)) | r1_partfun1(C_31, D_32) | ~m1_subset_1(D_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_29))) | ~v1_funct_2(D_32, A_30, B_29) | ~v1_funct_1(D_32) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_30, B_29))) | ~v1_funct_1(C_31))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.56/1.40  tff(c_34, plain, (![D_20]: (r1_partfun1('#skF_3', '#skF_4') | k1_funct_1('#skF_3', D_20)=k1_funct_1('#skF_4', D_20) | ~r2_hidden(D_20, k1_relset_1('#skF_2', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.40  tff(c_36, plain, (![D_20]: (k1_funct_1('#skF_3', D_20)=k1_funct_1('#skF_4', D_20) | ~r2_hidden(D_20, k1_relset_1('#skF_2', '#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_35, c_34])).
% 2.56/1.40  tff(c_50, plain, (![D_32]: (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_2', '#skF_3', D_32))=k1_funct_1('#skF_4', '#skF_1'('#skF_2', '#skF_2', '#skF_3', D_32)) | k1_xboole_0='#skF_2' | r1_partfun1('#skF_3', D_32) | ~m1_subset_1(D_32, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(D_32, '#skF_2', '#skF_2') | ~v1_funct_1(D_32) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_43, c_36])).
% 2.56/1.40  tff(c_54, plain, (![D_32]: (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_2', '#skF_3', D_32))=k1_funct_1('#skF_4', '#skF_1'('#skF_2', '#skF_2', '#skF_3', D_32)) | k1_xboole_0='#skF_2' | r1_partfun1('#skF_3', D_32) | ~m1_subset_1(D_32, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(D_32, '#skF_2', '#skF_2') | ~v1_funct_1(D_32))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_50])).
% 2.56/1.40  tff(c_55, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_54])).
% 2.56/1.40  tff(c_6, plain, (![B_2, C_3, D_9]: (r2_hidden('#skF_1'(k1_xboole_0, B_2, C_3, D_9), k1_relset_1(k1_xboole_0, B_2, C_3)) | r1_partfun1(C_3, D_9) | ~m1_subset_1(D_9, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_2(D_9, k1_xboole_0, B_2) | ~v1_funct_1(D_9) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.56/1.40  tff(c_81, plain, (![B_38, C_39, D_40]: (r2_hidden('#skF_1'('#skF_2', B_38, C_39, D_40), k1_relset_1('#skF_2', B_38, C_39)) | r1_partfun1(C_39, D_40) | ~m1_subset_1(D_40, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_38))) | ~v1_funct_2(D_40, '#skF_2', B_38) | ~v1_funct_1(D_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_38))) | ~v1_funct_1(C_39))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_55, c_55, c_55, c_6])).
% 2.56/1.40  tff(c_85, plain, (![D_40]: (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_2', '#skF_3', D_40))=k1_funct_1('#skF_4', '#skF_1'('#skF_2', '#skF_2', '#skF_3', D_40)) | r1_partfun1('#skF_3', D_40) | ~m1_subset_1(D_40, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(D_40, '#skF_2', '#skF_2') | ~v1_funct_1(D_40) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_81, c_36])).
% 2.56/1.40  tff(c_89, plain, (![D_41]: (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_2', '#skF_3', D_41))=k1_funct_1('#skF_4', '#skF_1'('#skF_2', '#skF_2', '#skF_3', D_41)) | r1_partfun1('#skF_3', D_41) | ~m1_subset_1(D_41, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(D_41, '#skF_2', '#skF_2') | ~v1_funct_1(D_41))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_85])).
% 2.56/1.40  tff(c_95, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_2', '#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_2', '#skF_2', '#skF_3', '#skF_4')) | r1_partfun1('#skF_3', '#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_89])).
% 2.56/1.40  tff(c_101, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_2', '#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_2', '#skF_2', '#skF_3', '#skF_4')) | r1_partfun1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_95])).
% 2.56/1.40  tff(c_102, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_2', '#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_2', '#skF_2', '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_35, c_101])).
% 2.56/1.40  tff(c_2, plain, (![D_9, B_2, C_3]: (k1_funct_1(D_9, '#skF_1'(k1_xboole_0, B_2, C_3, D_9))!=k1_funct_1(C_3, '#skF_1'(k1_xboole_0, B_2, C_3, D_9)) | r1_partfun1(C_3, D_9) | ~m1_subset_1(D_9, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_2(D_9, k1_xboole_0, B_2) | ~v1_funct_1(D_9) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.56/1.40  tff(c_134, plain, (![D_55, B_56, C_57]: (k1_funct_1(D_55, '#skF_1'('#skF_2', B_56, C_57, D_55))!=k1_funct_1(C_57, '#skF_1'('#skF_2', B_56, C_57, D_55)) | r1_partfun1(C_57, D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_56))) | ~v1_funct_2(D_55, '#skF_2', B_56) | ~v1_funct_1(D_55) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_56))) | ~v1_funct_1(C_57))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_55, c_55, c_55, c_2])).
% 2.56/1.40  tff(c_136, plain, (r1_partfun1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_102, c_134])).
% 2.56/1.40  tff(c_139, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_16, c_14, c_136])).
% 2.56/1.40  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_139])).
% 2.56/1.40  tff(c_143, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_54])).
% 2.56/1.40  tff(c_144, plain, (![D_58]: (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_2', '#skF_3', D_58))=k1_funct_1('#skF_4', '#skF_1'('#skF_2', '#skF_2', '#skF_3', D_58)) | r1_partfun1('#skF_3', D_58) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(D_58, '#skF_2', '#skF_2') | ~v1_funct_1(D_58))), inference(splitRight, [status(thm)], [c_54])).
% 2.56/1.40  tff(c_150, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_2', '#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_2', '#skF_2', '#skF_3', '#skF_4')) | r1_partfun1('#skF_3', '#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_144])).
% 2.56/1.40  tff(c_156, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_2', '#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_2', '#skF_2', '#skF_3', '#skF_4')) | r1_partfun1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_150])).
% 2.56/1.40  tff(c_157, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_2', '#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_2', '#skF_2', '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_35, c_156])).
% 2.56/1.40  tff(c_177, plain, (![B_67, D_68, A_69, C_70]: (k1_xboole_0=B_67 | k1_funct_1(D_68, '#skF_1'(A_69, B_67, C_70, D_68))!=k1_funct_1(C_70, '#skF_1'(A_69, B_67, C_70, D_68)) | r1_partfun1(C_70, D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_67))) | ~v1_funct_2(D_68, A_69, B_67) | ~v1_funct_1(D_68) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_69, B_67))) | ~v1_funct_1(C_70))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.56/1.40  tff(c_179, plain, (k1_xboole_0='#skF_2' | r1_partfun1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_157, c_177])).
% 2.56/1.40  tff(c_182, plain, (k1_xboole_0='#skF_2' | r1_partfun1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_16, c_14, c_179])).
% 2.56/1.40  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_143, c_182])).
% 2.56/1.40  tff(c_185, plain, (k1_funct_1('#skF_3', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_24])).
% 2.56/1.40  tff(c_186, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_24])).
% 2.56/1.40  tff(c_26, plain, (r2_hidden('#skF_5', k1_relset_1('#skF_2', '#skF_2', '#skF_3')) | ~r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.40  tff(c_188, plain, (r2_hidden('#skF_5', k1_relset_1('#skF_2', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_26])).
% 2.56/1.40  tff(c_206, plain, (![E_88, B_89, C_90, A_91, D_87]: (k1_xboole_0=B_89 | k1_funct_1(D_87, E_88)=k1_funct_1(C_90, E_88) | ~r2_hidden(E_88, k1_relset_1(A_91, B_89, C_90)) | ~r1_partfun1(C_90, D_87) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1(A_91, B_89))) | ~v1_funct_2(D_87, A_91, B_89) | ~v1_funct_1(D_87) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_89))) | ~v1_funct_1(C_90))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.56/1.40  tff(c_212, plain, (![D_87]: (k1_xboole_0='#skF_2' | k1_funct_1(D_87, '#skF_5')=k1_funct_1('#skF_3', '#skF_5') | ~r1_partfun1('#skF_3', D_87) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(D_87, '#skF_2', '#skF_2') | ~v1_funct_1(D_87) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_188, c_206])).
% 2.56/1.40  tff(c_217, plain, (![D_87]: (k1_xboole_0='#skF_2' | k1_funct_1(D_87, '#skF_5')=k1_funct_1('#skF_3', '#skF_5') | ~r1_partfun1('#skF_3', D_87) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(D_87, '#skF_2', '#skF_2') | ~v1_funct_1(D_87))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_212])).
% 2.56/1.40  tff(c_218, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_217])).
% 2.56/1.40  tff(c_10, plain, (![D_9, E_12, C_3, B_2]: (k1_funct_1(D_9, E_12)=k1_funct_1(C_3, E_12) | ~r2_hidden(E_12, k1_relset_1(k1_xboole_0, B_2, C_3)) | ~r1_partfun1(C_3, D_9) | ~m1_subset_1(D_9, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_2(D_9, k1_xboole_0, B_2) | ~v1_funct_1(D_9) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.56/1.40  tff(c_259, plain, (![D_104, E_105, C_106, B_107]: (k1_funct_1(D_104, E_105)=k1_funct_1(C_106, E_105) | ~r2_hidden(E_105, k1_relset_1('#skF_2', B_107, C_106)) | ~r1_partfun1(C_106, D_104) | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_107))) | ~v1_funct_2(D_104, '#skF_2', B_107) | ~v1_funct_1(D_104) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_107))) | ~v1_funct_1(C_106))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_218, c_218, c_218, c_10])).
% 2.56/1.40  tff(c_263, plain, (![D_104]: (k1_funct_1(D_104, '#skF_5')=k1_funct_1('#skF_3', '#skF_5') | ~r1_partfun1('#skF_3', D_104) | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(D_104, '#skF_2', '#skF_2') | ~v1_funct_1(D_104) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_188, c_259])).
% 2.56/1.40  tff(c_268, plain, (![D_108]: (k1_funct_1(D_108, '#skF_5')=k1_funct_1('#skF_3', '#skF_5') | ~r1_partfun1('#skF_3', D_108) | ~m1_subset_1(D_108, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(D_108, '#skF_2', '#skF_2') | ~v1_funct_1(D_108))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_263])).
% 2.56/1.40  tff(c_274, plain, (k1_funct_1('#skF_3', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~r1_partfun1('#skF_3', '#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_268])).
% 2.56/1.40  tff(c_280, plain, (k1_funct_1('#skF_3', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_186, c_274])).
% 2.56/1.40  tff(c_282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_280])).
% 2.56/1.40  tff(c_285, plain, (![D_109]: (k1_funct_1(D_109, '#skF_5')=k1_funct_1('#skF_3', '#skF_5') | ~r1_partfun1('#skF_3', D_109) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(D_109, '#skF_2', '#skF_2') | ~v1_funct_1(D_109))), inference(splitRight, [status(thm)], [c_217])).
% 2.56/1.40  tff(c_291, plain, (k1_funct_1('#skF_3', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~r1_partfun1('#skF_3', '#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_285])).
% 2.56/1.40  tff(c_298, plain, (k1_funct_1('#skF_3', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_186, c_291])).
% 2.56/1.40  tff(c_300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_298])).
% 2.56/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.40  
% 2.56/1.40  Inference rules
% 2.56/1.40  ----------------------
% 2.56/1.40  #Ref     : 6
% 2.56/1.40  #Sup     : 42
% 2.56/1.40  #Fact    : 0
% 2.56/1.40  #Define  : 0
% 2.56/1.40  #Split   : 6
% 2.56/1.40  #Chain   : 0
% 2.56/1.40  #Close   : 0
% 2.56/1.40  
% 2.56/1.40  Ordering : KBO
% 2.56/1.40  
% 2.56/1.40  Simplification rules
% 2.56/1.40  ----------------------
% 2.56/1.40  #Subsume      : 9
% 2.56/1.40  #Demod        : 92
% 2.56/1.40  #Tautology    : 13
% 2.56/1.40  #SimpNegUnit  : 7
% 2.56/1.40  #BackRed      : 10
% 2.56/1.40  
% 2.56/1.40  #Partial instantiations: 0
% 2.56/1.40  #Strategies tried      : 1
% 2.56/1.40  
% 2.56/1.40  Timing (in seconds)
% 2.56/1.40  ----------------------
% 2.56/1.40  Preprocessing        : 0.32
% 2.56/1.40  Parsing              : 0.16
% 2.56/1.40  CNF conversion       : 0.02
% 2.56/1.40  Main loop            : 0.25
% 2.56/1.40  Inferencing          : 0.10
% 2.56/1.40  Reduction            : 0.08
% 2.56/1.40  Demodulation         : 0.05
% 2.56/1.40  BG Simplification    : 0.02
% 2.56/1.40  Subsumption          : 0.04
% 2.56/1.41  Abstraction          : 0.02
% 2.56/1.41  MUC search           : 0.00
% 2.56/1.41  Cooper               : 0.00
% 2.56/1.41  Total                : 0.61
% 2.56/1.41  Index Insertion      : 0.00
% 2.56/1.41  Index Deletion       : 0.00
% 2.56/1.41  Index Matching       : 0.00
% 2.56/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
