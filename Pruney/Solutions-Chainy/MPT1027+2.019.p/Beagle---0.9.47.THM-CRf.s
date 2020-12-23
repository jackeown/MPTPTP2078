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
% DateTime   : Thu Dec  3 10:16:44 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   90 (1914 expanded)
%              Number of leaves         :   24 ( 621 expanded)
%              Depth                    :   12
%              Number of atoms          :  143 (4733 expanded)
%              Number of equality atoms :   50 (1114 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_70,axiom,(
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

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26])).

tff(c_28,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( v1_xboole_0(k2_zfmisc_1(A_6,B_7))
      | ~ v1_xboole_0(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_51,plain,(
    ! [B_21,A_22] :
      ( v1_xboole_0(B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_22))
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_55,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_51])).

tff(c_56,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_56])).

tff(c_156,plain,(
    ! [B_42,C_43,A_44] :
      ( k1_xboole_0 = B_42
      | v1_funct_2(C_43,A_44,B_42)
      | k1_relset_1(A_44,B_42,C_43) != A_44
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_165,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_156])).

tff(c_169,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_165])).

tff(c_170,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_169])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_61,plain,(
    ! [B_23,A_24] :
      ( ~ r1_xboole_0(B_23,A_24)
      | ~ r1_tarski(B_23,A_24)
      | v1_xboole_0(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,(
    ! [A_25] :
      ( ~ r1_tarski(A_25,k1_xboole_0)
      | v1_xboole_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_6,c_61])).

tff(c_71,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_66])).

tff(c_181,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_71])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_181])).

tff(c_190,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_189,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_197,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_189,c_2])).

tff(c_226,plain,(
    ! [A_50] :
      ( A_50 = '#skF_3'
      | ~ v1_xboole_0(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_2])).

tff(c_236,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_190,c_226])).

tff(c_241,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_30])).

tff(c_42,plain,(
    ! [A_17,B_18] :
      ( v1_xboole_0(k2_zfmisc_1(A_17,B_18))
      | ~ v1_xboole_0(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    ! [A_17,B_18] :
      ( k2_zfmisc_1(A_17,B_18) = k1_xboole_0
      | ~ v1_xboole_0(B_18) ) ),
    inference(resolution,[status(thm)],[c_42,c_2])).

tff(c_196,plain,(
    ! [A_17] : k2_zfmisc_1(A_17,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_189,c_46])).

tff(c_208,plain,(
    ! [A_17] : k2_zfmisc_1(A_17,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_196])).

tff(c_14,plain,(
    ! [A_11] :
      ( v1_funct_2(k1_xboole_0,A_11,k1_xboole_0)
      | k1_xboole_0 = A_11
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_11,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_258,plain,(
    ! [A_11] :
      ( v1_funct_2('#skF_3',A_11,'#skF_3')
      | A_11 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_208,c_197,c_197,c_197,c_197,c_197,c_14])).

tff(c_20,plain,(
    ! [B_12,C_13,A_11] :
      ( k1_xboole_0 = B_12
      | v1_funct_2(C_13,A_11,B_12)
      | k1_relset_1(A_11,B_12,C_13) != A_11
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_533,plain,(
    ! [B_87,C_88,A_89] :
      ( B_87 = '#skF_3'
      | v1_funct_2(C_88,A_89,B_87)
      | k1_relset_1(A_89,B_87,C_88) != A_89
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_87))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_20])).

tff(c_539,plain,(
    ! [C_88] :
      ( '#skF_2' = '#skF_3'
      | v1_funct_2(C_88,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_88) != '#skF_1'
      | ~ m1_subset_1(C_88,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_533])).

tff(c_544,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_539])).

tff(c_547,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_34])).

tff(c_556,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_258,c_547])).

tff(c_353,plain,(
    ! [B_66,C_67,A_68] :
      ( B_66 = '#skF_3'
      | v1_funct_2(C_67,A_68,B_66)
      | k1_relset_1(A_68,B_66,C_67) != A_68
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_66))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_20])).

tff(c_359,plain,(
    ! [C_67] :
      ( '#skF_2' = '#skF_3'
      | v1_funct_2(C_67,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_67) != '#skF_1'
      | ~ m1_subset_1(C_67,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_353])).

tff(c_364,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_359])).

tff(c_379,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_34])).

tff(c_388,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_258,c_379])).

tff(c_378,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_28])).

tff(c_459,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_388,c_378])).

tff(c_18,plain,(
    ! [C_13,B_12] :
      ( v1_funct_2(C_13,k1_xboole_0,B_12)
      | k1_relset_1(k1_xboole_0,B_12,C_13) != k1_xboole_0
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_315,plain,(
    ! [C_60,B_61] :
      ( v1_funct_2(C_60,'#skF_3',B_61)
      | k1_relset_1('#skF_3',B_61,C_60) != '#skF_3'
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_61))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_197,c_197,c_197,c_18])).

tff(c_324,plain,(
    ! [C_62] :
      ( v1_funct_2(C_62,'#skF_3','#skF_3')
      | k1_relset_1('#skF_3','#skF_3',C_62) != '#skF_3'
      | ~ m1_subset_1(C_62,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_315])).

tff(c_328,plain,
    ( v1_funct_2('#skF_3','#skF_3','#skF_3')
    | k1_relset_1('#skF_3','#skF_3','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_241,c_324])).

tff(c_329,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_3') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_328])).

tff(c_396,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_388,c_388,c_388,c_329])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_396])).

tff(c_494,plain,(
    ! [C_83] :
      ( v1_funct_2(C_83,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_83) != '#skF_1'
      | ~ m1_subset_1(C_83,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_359])).

tff(c_497,plain,
    ( v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_241,c_494])).

tff(c_500,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_497])).

tff(c_502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_500])).

tff(c_503,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_573,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_556,c_556,c_503])).

tff(c_567,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_556,c_547])).

tff(c_637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_567])).

tff(c_640,plain,(
    ! [C_100] :
      ( v1_funct_2(C_100,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_100) != '#skF_1'
      | ~ m1_subset_1(C_100,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_539])).

tff(c_643,plain,
    ( v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_241,c_640])).

tff(c_646,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_643])).

tff(c_648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_646])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.41  
% 2.80/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.42  %$ v1_funct_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.80/1.42  
% 2.80/1.42  %Foreground sorts:
% 2.80/1.42  
% 2.80/1.42  
% 2.80/1.42  %Background operators:
% 2.80/1.42  
% 2.80/1.42  
% 2.80/1.42  %Foreground operators:
% 2.80/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.80/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.80/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.80/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.80/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.80/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.80/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.80/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.42  
% 2.80/1.43  tff(f_83, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 2.80/1.43  tff(f_45, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 2.80/1.43  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.80/1.43  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.80/1.43  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.80/1.43  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.80/1.43  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.80/1.43  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.80/1.43  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.80/1.43  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.80/1.43  tff(c_26, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.80/1.43  tff(c_34, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26])).
% 2.80/1.43  tff(c_28, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.80/1.43  tff(c_10, plain, (![A_6, B_7]: (v1_xboole_0(k2_zfmisc_1(A_6, B_7)) | ~v1_xboole_0(B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.80/1.43  tff(c_51, plain, (![B_21, A_22]: (v1_xboole_0(B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_22)) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.80/1.43  tff(c_55, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_51])).
% 2.80/1.43  tff(c_56, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_55])).
% 2.80/1.43  tff(c_60, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_10, c_56])).
% 2.80/1.43  tff(c_156, plain, (![B_42, C_43, A_44]: (k1_xboole_0=B_42 | v1_funct_2(C_43, A_44, B_42) | k1_relset_1(A_44, B_42, C_43)!=A_44 | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_42))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.80/1.43  tff(c_165, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_30, c_156])).
% 2.80/1.43  tff(c_169, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_165])).
% 2.80/1.43  tff(c_170, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_34, c_169])).
% 2.80/1.43  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.43  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.80/1.43  tff(c_61, plain, (![B_23, A_24]: (~r1_xboole_0(B_23, A_24) | ~r1_tarski(B_23, A_24) | v1_xboole_0(B_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.80/1.43  tff(c_66, plain, (![A_25]: (~r1_tarski(A_25, k1_xboole_0) | v1_xboole_0(A_25))), inference(resolution, [status(thm)], [c_6, c_61])).
% 2.80/1.43  tff(c_71, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_66])).
% 2.80/1.43  tff(c_181, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_71])).
% 2.80/1.43  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_181])).
% 2.80/1.43  tff(c_190, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_55])).
% 2.80/1.43  tff(c_189, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_55])).
% 2.80/1.43  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.80/1.43  tff(c_197, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_189, c_2])).
% 2.80/1.43  tff(c_226, plain, (![A_50]: (A_50='#skF_3' | ~v1_xboole_0(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_2])).
% 2.80/1.43  tff(c_236, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_190, c_226])).
% 2.80/1.43  tff(c_241, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_30])).
% 2.80/1.43  tff(c_42, plain, (![A_17, B_18]: (v1_xboole_0(k2_zfmisc_1(A_17, B_18)) | ~v1_xboole_0(B_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.80/1.43  tff(c_46, plain, (![A_17, B_18]: (k2_zfmisc_1(A_17, B_18)=k1_xboole_0 | ~v1_xboole_0(B_18))), inference(resolution, [status(thm)], [c_42, c_2])).
% 2.80/1.43  tff(c_196, plain, (![A_17]: (k2_zfmisc_1(A_17, '#skF_3')=k1_xboole_0)), inference(resolution, [status(thm)], [c_189, c_46])).
% 2.80/1.43  tff(c_208, plain, (![A_17]: (k2_zfmisc_1(A_17, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_196])).
% 2.80/1.43  tff(c_14, plain, (![A_11]: (v1_funct_2(k1_xboole_0, A_11, k1_xboole_0) | k1_xboole_0=A_11 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_11, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.80/1.43  tff(c_258, plain, (![A_11]: (v1_funct_2('#skF_3', A_11, '#skF_3') | A_11='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_208, c_197, c_197, c_197, c_197, c_197, c_14])).
% 2.80/1.43  tff(c_20, plain, (![B_12, C_13, A_11]: (k1_xboole_0=B_12 | v1_funct_2(C_13, A_11, B_12) | k1_relset_1(A_11, B_12, C_13)!=A_11 | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.80/1.43  tff(c_533, plain, (![B_87, C_88, A_89]: (B_87='#skF_3' | v1_funct_2(C_88, A_89, B_87) | k1_relset_1(A_89, B_87, C_88)!=A_89 | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_87))))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_20])).
% 2.80/1.43  tff(c_539, plain, (![C_88]: ('#skF_2'='#skF_3' | v1_funct_2(C_88, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_88)!='#skF_1' | ~m1_subset_1(C_88, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_236, c_533])).
% 2.80/1.43  tff(c_544, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_539])).
% 2.80/1.43  tff(c_547, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_544, c_34])).
% 2.80/1.43  tff(c_556, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_258, c_547])).
% 2.80/1.43  tff(c_353, plain, (![B_66, C_67, A_68]: (B_66='#skF_3' | v1_funct_2(C_67, A_68, B_66) | k1_relset_1(A_68, B_66, C_67)!=A_68 | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_66))))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_20])).
% 2.80/1.43  tff(c_359, plain, (![C_67]: ('#skF_2'='#skF_3' | v1_funct_2(C_67, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_67)!='#skF_1' | ~m1_subset_1(C_67, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_236, c_353])).
% 2.80/1.43  tff(c_364, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_359])).
% 2.80/1.43  tff(c_379, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_364, c_34])).
% 2.80/1.43  tff(c_388, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_258, c_379])).
% 2.80/1.43  tff(c_378, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_364, c_28])).
% 2.80/1.43  tff(c_459, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_388, c_388, c_378])).
% 2.80/1.43  tff(c_18, plain, (![C_13, B_12]: (v1_funct_2(C_13, k1_xboole_0, B_12) | k1_relset_1(k1_xboole_0, B_12, C_13)!=k1_xboole_0 | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_12))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.80/1.43  tff(c_315, plain, (![C_60, B_61]: (v1_funct_2(C_60, '#skF_3', B_61) | k1_relset_1('#skF_3', B_61, C_60)!='#skF_3' | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_61))))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_197, c_197, c_197, c_18])).
% 2.80/1.43  tff(c_324, plain, (![C_62]: (v1_funct_2(C_62, '#skF_3', '#skF_3') | k1_relset_1('#skF_3', '#skF_3', C_62)!='#skF_3' | ~m1_subset_1(C_62, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_208, c_315])).
% 2.80/1.43  tff(c_328, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_3') | k1_relset_1('#skF_3', '#skF_3', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_241, c_324])).
% 2.80/1.43  tff(c_329, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_3')!='#skF_3'), inference(splitLeft, [status(thm)], [c_328])).
% 2.80/1.43  tff(c_396, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_388, c_388, c_388, c_388, c_329])).
% 2.80/1.43  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_459, c_396])).
% 2.80/1.43  tff(c_494, plain, (![C_83]: (v1_funct_2(C_83, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_83)!='#skF_1' | ~m1_subset_1(C_83, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_359])).
% 2.80/1.43  tff(c_497, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_241, c_494])).
% 2.80/1.43  tff(c_500, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_497])).
% 2.80/1.43  tff(c_502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_500])).
% 2.80/1.43  tff(c_503, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_328])).
% 2.80/1.43  tff(c_573, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_556, c_556, c_556, c_503])).
% 2.80/1.43  tff(c_567, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_556, c_556, c_547])).
% 2.80/1.43  tff(c_637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_573, c_567])).
% 2.80/1.43  tff(c_640, plain, (![C_100]: (v1_funct_2(C_100, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_100)!='#skF_1' | ~m1_subset_1(C_100, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_539])).
% 2.80/1.43  tff(c_643, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_241, c_640])).
% 2.80/1.43  tff(c_646, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_643])).
% 2.80/1.43  tff(c_648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_646])).
% 2.80/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.43  
% 2.80/1.43  Inference rules
% 2.80/1.43  ----------------------
% 2.80/1.43  #Ref     : 0
% 2.80/1.43  #Sup     : 120
% 2.80/1.43  #Fact    : 0
% 2.80/1.43  #Define  : 0
% 2.80/1.43  #Split   : 5
% 2.80/1.43  #Chain   : 0
% 2.80/1.43  #Close   : 0
% 2.80/1.43  
% 2.80/1.43  Ordering : KBO
% 2.80/1.43  
% 2.80/1.43  Simplification rules
% 2.80/1.43  ----------------------
% 2.80/1.43  #Subsume      : 11
% 2.80/1.43  #Demod        : 242
% 2.80/1.43  #Tautology    : 75
% 2.80/1.43  #SimpNegUnit  : 6
% 2.80/1.43  #BackRed      : 75
% 2.80/1.43  
% 2.80/1.43  #Partial instantiations: 0
% 2.80/1.43  #Strategies tried      : 1
% 2.80/1.43  
% 2.80/1.43  Timing (in seconds)
% 2.80/1.43  ----------------------
% 2.80/1.44  Preprocessing        : 0.30
% 2.80/1.44  Parsing              : 0.17
% 2.80/1.44  CNF conversion       : 0.02
% 2.80/1.44  Main loop            : 0.32
% 2.80/1.44  Inferencing          : 0.11
% 2.80/1.44  Reduction            : 0.10
% 2.80/1.44  Demodulation         : 0.07
% 2.80/1.44  BG Simplification    : 0.02
% 2.80/1.44  Subsumption          : 0.07
% 2.80/1.44  Abstraction          : 0.01
% 2.80/1.44  MUC search           : 0.00
% 2.80/1.44  Cooper               : 0.00
% 2.80/1.44  Total                : 0.66
% 2.80/1.44  Index Insertion      : 0.00
% 2.80/1.44  Index Deletion       : 0.00
% 2.80/1.44  Index Matching       : 0.00
% 2.80/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
