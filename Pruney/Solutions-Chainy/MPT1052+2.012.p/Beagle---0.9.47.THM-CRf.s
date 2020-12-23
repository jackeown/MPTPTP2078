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
% DateTime   : Thu Dec  3 10:17:10 EST 2020

% Result     : Theorem 9.47s
% Output     : CNFRefutation 9.71s
% Verified   : 
% Statistics : Number of formulae       :  199 (2428 expanded)
%              Number of leaves         :   41 ( 791 expanded)
%              Depth                    :   15
%              Number of atoms          :  309 (5266 expanded)
%              Number of equality atoms :  128 (1373 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_82,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_9969,plain,(
    ! [A_1519,B_1520] :
      ( k2_xboole_0(A_1519,B_1520) = B_1520
      | ~ r1_tarski(A_1519,B_1520) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_9983,plain,(
    ! [A_1523] : k2_xboole_0(k1_xboole_0,A_1523) = A_1523 ),
    inference(resolution,[status(thm)],[c_14,c_9969])).

tff(c_10003,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9983])).

tff(c_9974,plain,(
    ! [A_1521,B_1522] :
      ( v1_xboole_0(k1_funct_2(A_1521,B_1522))
      | ~ v1_xboole_0(B_1522)
      | v1_xboole_0(A_1521) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_66,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_118,plain,(
    ! [B_41,A_42] :
      ( ~ r2_hidden(B_41,A_42)
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_122,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_66,c_118])).

tff(c_9981,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_9974,c_122])).

tff(c_10006,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_9981])).

tff(c_64,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_173,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_244,plain,(
    ! [A_57,B_58] :
      ( v1_xboole_0(k1_funct_2(A_57,B_58))
      | ~ v1_xboole_0(B_58)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_251,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_244,c_122])).

tff(c_256,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_70,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_443,plain,(
    ! [C_81,A_82,B_83] :
      ( m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ r2_hidden(C_81,k1_funct_2(A_82,B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_561,plain,(
    ! [C_95,A_96,B_97] :
      ( r1_tarski(C_95,k2_zfmisc_1(A_96,B_97))
      | ~ r2_hidden(C_95,k1_funct_2(A_96,B_97)) ) ),
    inference(resolution,[status(thm)],[c_443,c_22])).

tff(c_582,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_66,c_561])).

tff(c_26,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( k2_relat_1(k2_zfmisc_1(A_17,B_18)) = B_18
      | k1_xboole_0 = B_18
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1303,plain,(
    ! [A_111,B_112] :
      ( r1_tarski(k2_relat_1(A_111),k2_relat_1(B_112))
      | ~ r1_tarski(A_111,B_112)
      | ~ v1_relat_1(B_112)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1312,plain,(
    ! [A_111,B_18,A_17] :
      ( r1_tarski(k2_relat_1(A_111),B_18)
      | ~ r1_tarski(A_111,k2_zfmisc_1(A_17,B_18))
      | ~ v1_relat_1(k2_zfmisc_1(A_17,B_18))
      | ~ v1_relat_1(A_111)
      | k1_xboole_0 = B_18
      | k1_xboole_0 = A_17 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1303])).

tff(c_4825,plain,(
    ! [A_1428,B_1429,A_1430] :
      ( r1_tarski(k2_relat_1(A_1428),B_1429)
      | ~ r1_tarski(A_1428,k2_zfmisc_1(A_1430,B_1429))
      | ~ v1_relat_1(A_1428)
      | k1_xboole_0 = B_1429
      | k1_xboole_0 = A_1430 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1312])).

tff(c_4835,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_582,c_4825])).

tff(c_4849,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4835])).

tff(c_4854,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4849])).

tff(c_179,plain,(
    ! [A_53,B_54] :
      ( k2_xboole_0(A_53,B_54) = B_54
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_184,plain,(
    ! [A_55] : k2_xboole_0(k1_xboole_0,A_55) = A_55 ),
    inference(resolution,[status(thm)],[c_14,c_179])).

tff(c_190,plain,(
    ! [A_55] : k2_xboole_0(A_55,k1_xboole_0) = A_55 ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_2])).

tff(c_4945,plain,(
    ! [A_55] : k2_xboole_0(A_55,'#skF_2') = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4854,c_190])).

tff(c_20,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4949,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_2',B_12) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4854,c_4854,c_20])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_586,plain,(
    k2_xboole_0('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) = k2_zfmisc_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_582,c_12])).

tff(c_5147,plain,(
    k2_xboole_0('#skF_4','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4949,c_4949,c_586])).

tff(c_5149,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4945,c_5147])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4953,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4854,c_4854,c_38])).

tff(c_5186,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5149,c_5149,c_4953])).

tff(c_5194,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5149,c_173])).

tff(c_5326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5186,c_5194])).

tff(c_5328,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4849])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( k1_relat_1(k2_zfmisc_1(A_17,B_18)) = A_17
      | k1_xboole_0 = B_18
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_508,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(k1_relat_1(A_91),k1_relat_1(B_92))
      | ~ r1_tarski(A_91,B_92)
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_517,plain,(
    ! [A_91,A_17,B_18] :
      ( r1_tarski(k1_relat_1(A_91),A_17)
      | ~ r1_tarski(A_91,k2_zfmisc_1(A_17,B_18))
      | ~ v1_relat_1(k2_zfmisc_1(A_17,B_18))
      | ~ v1_relat_1(A_91)
      | k1_xboole_0 = B_18
      | k1_xboole_0 = A_17 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_508])).

tff(c_5350,plain,(
    ! [A_1442,A_1443,B_1444] :
      ( r1_tarski(k1_relat_1(A_1442),A_1443)
      | ~ r1_tarski(A_1442,k2_zfmisc_1(A_1443,B_1444))
      | ~ v1_relat_1(A_1442)
      | k1_xboole_0 = B_1444
      | k1_xboole_0 = A_1443 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_517])).

tff(c_5360,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_582,c_5350])).

tff(c_5374,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5360])).

tff(c_5375,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_5328,c_5374])).

tff(c_5386,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5375])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5488,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5386,c_8])).

tff(c_5490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_256,c_5488])).

tff(c_5492,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5375])).

tff(c_399,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_funct_2(C_70,A_71,B_72)
      | ~ r2_hidden(C_70,k1_funct_2(A_71,B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_417,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_399])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1449,plain,(
    ! [A_118,B_119,C_120] :
      ( k1_relset_1(A_118,B_119,C_120) = k1_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1590,plain,(
    ! [A_139,B_140,A_141] :
      ( k1_relset_1(A_139,B_140,A_141) = k1_relat_1(A_141)
      | ~ r1_tarski(A_141,k2_zfmisc_1(A_139,B_140)) ) ),
    inference(resolution,[status(thm)],[c_24,c_1449])).

tff(c_1608,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_582,c_1590])).

tff(c_2431,plain,(
    ! [B_1340,A_1341,C_1342] :
      ( k1_xboole_0 = B_1340
      | k1_relset_1(A_1341,B_1340,C_1342) = A_1341
      | ~ v1_funct_2(C_1342,A_1341,B_1340)
      | ~ m1_subset_1(C_1342,k1_zfmisc_1(k2_zfmisc_1(A_1341,B_1340))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_9054,plain,(
    ! [B_1469,A_1470,A_1471] :
      ( k1_xboole_0 = B_1469
      | k1_relset_1(A_1470,B_1469,A_1471) = A_1470
      | ~ v1_funct_2(A_1471,A_1470,B_1469)
      | ~ r1_tarski(A_1471,k2_zfmisc_1(A_1470,B_1469)) ) ),
    inference(resolution,[status(thm)],[c_24,c_2431])).

tff(c_9075,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_582,c_9054])).

tff(c_9094,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_1608,c_9075])).

tff(c_9096,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_5492,c_9094])).

tff(c_9098,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9106,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9098,c_10])).

tff(c_9097,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_9102,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_9097,c_10])).

tff(c_9122,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9106,c_9102])).

tff(c_9107,plain,(
    ! [A_55] : k2_xboole_0(A_55,'#skF_2') = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9102,c_190])).

tff(c_9245,plain,(
    ! [A_55] : k2_xboole_0(A_55,'#skF_3') = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9122,c_9107])).

tff(c_9131,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9122,c_66])).

tff(c_18,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_9110,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9102,c_9102,c_18])).

tff(c_9186,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9122,c_9122,c_9110])).

tff(c_9791,plain,(
    ! [C_1505,A_1506,B_1507] :
      ( m1_subset_1(C_1505,k1_zfmisc_1(k2_zfmisc_1(A_1506,B_1507)))
      | ~ r2_hidden(C_1505,k1_funct_2(A_1506,B_1507)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_9818,plain,(
    ! [C_1511,A_1512] :
      ( m1_subset_1(C_1511,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(C_1511,k1_funct_2(A_1512,'#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9186,c_9791])).

tff(c_9844,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_9131,c_9818])).

tff(c_9849,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_9844,c_22])).

tff(c_9852,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9849,c_12])).

tff(c_9854,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9245,c_9852])).

tff(c_9115,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9102,c_9102,c_38])).

tff(c_9143,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9122,c_9122,c_9115])).

tff(c_9891,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9854,c_9854,c_9143])).

tff(c_9129,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9122,c_173])).

tff(c_9888,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9854,c_9129])).

tff(c_9957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9891,c_9888])).

tff(c_9958,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_10232,plain,(
    ! [C_1545,A_1546,B_1547] :
      ( m1_subset_1(C_1545,k1_zfmisc_1(k2_zfmisc_1(A_1546,B_1547)))
      | ~ r2_hidden(C_1545,k1_funct_2(A_1546,B_1547)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_13840,plain,(
    ! [C_1723,A_1724,B_1725] :
      ( r1_tarski(C_1723,k2_zfmisc_1(A_1724,B_1725))
      | ~ r2_hidden(C_1723,k1_funct_2(A_1724,B_1725)) ) ),
    inference(resolution,[status(thm)],[c_10232,c_22])).

tff(c_13861,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_66,c_13840])).

tff(c_13866,plain,(
    ! [A_1726,B_1727] :
      ( r1_tarski(k2_relat_1(A_1726),k2_relat_1(B_1727))
      | ~ r1_tarski(A_1726,B_1727)
      | ~ v1_relat_1(B_1727)
      | ~ v1_relat_1(A_1726) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_13875,plain,(
    ! [A_1726,B_18,A_17] :
      ( r1_tarski(k2_relat_1(A_1726),B_18)
      | ~ r1_tarski(A_1726,k2_zfmisc_1(A_17,B_18))
      | ~ v1_relat_1(k2_zfmisc_1(A_17,B_18))
      | ~ v1_relat_1(A_1726)
      | k1_xboole_0 = B_18
      | k1_xboole_0 = A_17 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_13866])).

tff(c_17211,plain,(
    ! [A_3187,B_3188,A_3189] :
      ( r1_tarski(k2_relat_1(A_3187),B_3188)
      | ~ r1_tarski(A_3187,k2_zfmisc_1(A_3189,B_3188))
      | ~ v1_relat_1(A_3187)
      | k1_xboole_0 = B_3188
      | k1_xboole_0 = A_3189 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_13875])).

tff(c_17219,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_13861,c_17211])).

tff(c_17232,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_17219])).

tff(c_17233,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_9958,c_17232])).

tff(c_17238,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_17233])).

tff(c_112,plain,(
    ! [A_39,B_40] : v1_relat_1(k2_zfmisc_1(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_114,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_112])).

tff(c_9959,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_10287,plain,(
    ! [A_1553,B_1554] :
      ( r1_tarski(k1_relat_1(A_1553),k1_relat_1(B_1554))
      | ~ r1_tarski(A_1553,B_1554)
      | ~ v1_relat_1(B_1554)
      | ~ v1_relat_1(A_1553) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10299,plain,(
    ! [B_1554] :
      ( r1_tarski('#skF_2',k1_relat_1(B_1554))
      | ~ r1_tarski('#skF_4',B_1554)
      | ~ v1_relat_1(B_1554)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9959,c_10287])).

tff(c_10332,plain,(
    ! [B_1557] :
      ( r1_tarski('#skF_2',k1_relat_1(B_1557))
      | ~ r1_tarski('#skF_4',B_1557)
      | ~ v1_relat_1(B_1557) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_10299])).

tff(c_10344,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_4',k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_10332])).

tff(c_10351,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_10344])).

tff(c_13781,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_10351])).

tff(c_17303,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17238,c_13781])).

tff(c_17327,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_2',B_12) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17238,c_17238,c_20])).

tff(c_17498,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17327,c_13861])).

tff(c_17500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17303,c_17498])).

tff(c_17501,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17233])).

tff(c_17596,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17501,c_8])).

tff(c_17598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10006,c_17596])).

tff(c_17599,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_10351])).

tff(c_17603,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_17599,c_12])).

tff(c_17605,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10003,c_17603])).

tff(c_17626,plain,(
    ! [A_1] : k2_xboole_0(A_1,'#skF_2') = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17605,c_10003])).

tff(c_17600,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_10351])).

tff(c_17652,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17605,c_17600])).

tff(c_17656,plain,(
    k2_xboole_0('#skF_4','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_17652,c_12])).

tff(c_17882,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17626,c_17656])).

tff(c_17633,plain,(
    ! [A_10] : r1_tarski('#skF_2',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17605,c_14])).

tff(c_17894,plain,(
    ! [A_10] : r1_tarski('#skF_4',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17882,c_17633])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_17634,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17605,c_17605,c_36])).

tff(c_17893,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17882,c_17882,c_17634])).

tff(c_17955,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17893,c_9958])).

tff(c_17958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17894,c_17955])).

tff(c_17960,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_9981])).

tff(c_17968,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_17960,c_10])).

tff(c_9989,plain,(
    ! [A_1523] : k2_xboole_0(A_1523,k1_xboole_0) = A_1523 ),
    inference(superposition,[status(thm),theory(equality)],[c_9983,c_2])).

tff(c_18029,plain,(
    ! [A_1523] : k2_xboole_0(A_1523,'#skF_3') = A_1523 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17968,c_9989])).

tff(c_17959,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_9981])).

tff(c_17964,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_17959,c_10])).

tff(c_17983,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17968,c_17964])).

tff(c_17992,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17983,c_66])).

tff(c_17972,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_2',B_12) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17964,c_17964,c_20])).

tff(c_18134,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_3',B_12) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17983,c_17983,c_17972])).

tff(c_18426,plain,(
    ! [C_3243,A_3244,B_3245] :
      ( m1_subset_1(C_3243,k1_zfmisc_1(k2_zfmisc_1(A_3244,B_3245)))
      | ~ r2_hidden(C_3243,k1_funct_2(A_3244,B_3245)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_18438,plain,(
    ! [C_3247,B_3248] :
      ( m1_subset_1(C_3247,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(C_3247,k1_funct_2('#skF_3',B_3248)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18134,c_18426])).

tff(c_18458,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_17992,c_18438])).

tff(c_18463,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_18458,c_22])).

tff(c_18466,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18463,c_12])).

tff(c_18468,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18029,c_18466])).

tff(c_17974,plain,(
    ! [A_10] : r1_tarski('#skF_2',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17964,c_14])).

tff(c_18005,plain,(
    ! [A_10] : r1_tarski('#skF_3',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17983,c_17974])).

tff(c_18496,plain,(
    ! [A_10] : r1_tarski('#skF_4',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18468,c_18005])).

tff(c_17975,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17964,c_17964,c_36])).

tff(c_18015,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17983,c_17983,c_17975])).

tff(c_18494,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18468,c_18468,c_18015])).

tff(c_18503,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18468,c_9958])).

tff(c_18547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18496,c_18494,c_18503])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.47/3.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.61/3.48  
% 9.61/3.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.61/3.49  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 9.61/3.49  
% 9.61/3.49  %Foreground sorts:
% 9.61/3.49  
% 9.61/3.49  
% 9.61/3.49  %Background operators:
% 9.61/3.49  
% 9.61/3.49  
% 9.61/3.49  %Foreground operators:
% 9.61/3.49  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 9.61/3.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.61/3.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.61/3.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.61/3.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.61/3.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.61/3.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.61/3.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.61/3.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.61/3.49  tff('#skF_2', type, '#skF_2': $i).
% 9.61/3.49  tff('#skF_3', type, '#skF_3': $i).
% 9.61/3.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.61/3.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.61/3.49  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 9.61/3.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.61/3.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.61/3.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.61/3.49  tff('#skF_4', type, '#skF_4': $i).
% 9.61/3.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.61/3.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.61/3.49  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 9.61/3.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.61/3.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.61/3.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.61/3.49  
% 9.71/3.51  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.71/3.51  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.71/3.51  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.71/3.51  tff(f_111, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_2)).
% 9.71/3.51  tff(f_132, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_2)).
% 9.71/3.51  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.71/3.51  tff(f_119, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 9.71/3.51  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.71/3.51  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.71/3.51  tff(f_68, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 9.71/3.51  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 9.71/3.51  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.71/3.51  tff(f_82, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 9.71/3.51  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.71/3.51  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.71/3.51  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.71/3.51  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.71/3.51  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.71/3.51  tff(c_14, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.71/3.51  tff(c_9969, plain, (![A_1519, B_1520]: (k2_xboole_0(A_1519, B_1520)=B_1520 | ~r1_tarski(A_1519, B_1520))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.71/3.51  tff(c_9983, plain, (![A_1523]: (k2_xboole_0(k1_xboole_0, A_1523)=A_1523)), inference(resolution, [status(thm)], [c_14, c_9969])).
% 9.71/3.51  tff(c_10003, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_9983])).
% 9.71/3.51  tff(c_9974, plain, (![A_1521, B_1522]: (v1_xboole_0(k1_funct_2(A_1521, B_1522)) | ~v1_xboole_0(B_1522) | v1_xboole_0(A_1521))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.71/3.51  tff(c_66, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.71/3.51  tff(c_118, plain, (![B_41, A_42]: (~r2_hidden(B_41, A_42) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.71/3.51  tff(c_122, plain, (~v1_xboole_0(k1_funct_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_66, c_118])).
% 9.71/3.51  tff(c_9981, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_9974, c_122])).
% 9.71/3.51  tff(c_10006, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_9981])).
% 9.71/3.51  tff(c_64, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_relat_1('#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.71/3.51  tff(c_173, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_64])).
% 9.71/3.51  tff(c_244, plain, (![A_57, B_58]: (v1_xboole_0(k1_funct_2(A_57, B_58)) | ~v1_xboole_0(B_58) | v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.71/3.51  tff(c_251, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_244, c_122])).
% 9.71/3.51  tff(c_256, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_251])).
% 9.71/3.51  tff(c_70, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.71/3.51  tff(c_443, plain, (![C_81, A_82, B_83]: (m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~r2_hidden(C_81, k1_funct_2(A_82, B_83)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.71/3.51  tff(c_22, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.71/3.51  tff(c_561, plain, (![C_95, A_96, B_97]: (r1_tarski(C_95, k2_zfmisc_1(A_96, B_97)) | ~r2_hidden(C_95, k1_funct_2(A_96, B_97)))), inference(resolution, [status(thm)], [c_443, c_22])).
% 9.71/3.51  tff(c_582, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_66, c_561])).
% 9.71/3.51  tff(c_26, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.71/3.51  tff(c_28, plain, (![A_17, B_18]: (k2_relat_1(k2_zfmisc_1(A_17, B_18))=B_18 | k1_xboole_0=B_18 | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.71/3.51  tff(c_1303, plain, (![A_111, B_112]: (r1_tarski(k2_relat_1(A_111), k2_relat_1(B_112)) | ~r1_tarski(A_111, B_112) | ~v1_relat_1(B_112) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.71/3.51  tff(c_1312, plain, (![A_111, B_18, A_17]: (r1_tarski(k2_relat_1(A_111), B_18) | ~r1_tarski(A_111, k2_zfmisc_1(A_17, B_18)) | ~v1_relat_1(k2_zfmisc_1(A_17, B_18)) | ~v1_relat_1(A_111) | k1_xboole_0=B_18 | k1_xboole_0=A_17)), inference(superposition, [status(thm), theory('equality')], [c_28, c_1303])).
% 9.71/3.51  tff(c_4825, plain, (![A_1428, B_1429, A_1430]: (r1_tarski(k2_relat_1(A_1428), B_1429) | ~r1_tarski(A_1428, k2_zfmisc_1(A_1430, B_1429)) | ~v1_relat_1(A_1428) | k1_xboole_0=B_1429 | k1_xboole_0=A_1430)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1312])).
% 9.71/3.51  tff(c_4835, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_582, c_4825])).
% 9.71/3.51  tff(c_4849, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4835])).
% 9.71/3.51  tff(c_4854, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4849])).
% 9.71/3.51  tff(c_179, plain, (![A_53, B_54]: (k2_xboole_0(A_53, B_54)=B_54 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.71/3.51  tff(c_184, plain, (![A_55]: (k2_xboole_0(k1_xboole_0, A_55)=A_55)), inference(resolution, [status(thm)], [c_14, c_179])).
% 9.71/3.51  tff(c_190, plain, (![A_55]: (k2_xboole_0(A_55, k1_xboole_0)=A_55)), inference(superposition, [status(thm), theory('equality')], [c_184, c_2])).
% 9.71/3.51  tff(c_4945, plain, (![A_55]: (k2_xboole_0(A_55, '#skF_2')=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_4854, c_190])).
% 9.71/3.51  tff(c_20, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.71/3.51  tff(c_4949, plain, (![B_12]: (k2_zfmisc_1('#skF_2', B_12)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4854, c_4854, c_20])).
% 9.71/3.51  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.71/3.51  tff(c_586, plain, (k2_xboole_0('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_582, c_12])).
% 9.71/3.51  tff(c_5147, plain, (k2_xboole_0('#skF_4', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4949, c_4949, c_586])).
% 9.71/3.51  tff(c_5149, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4945, c_5147])).
% 9.71/3.51  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.71/3.51  tff(c_4953, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4854, c_4854, c_38])).
% 9.71/3.51  tff(c_5186, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5149, c_5149, c_4953])).
% 9.71/3.51  tff(c_5194, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5149, c_173])).
% 9.71/3.51  tff(c_5326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5186, c_5194])).
% 9.71/3.51  tff(c_5328, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_4849])).
% 9.71/3.51  tff(c_30, plain, (![A_17, B_18]: (k1_relat_1(k2_zfmisc_1(A_17, B_18))=A_17 | k1_xboole_0=B_18 | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.71/3.51  tff(c_508, plain, (![A_91, B_92]: (r1_tarski(k1_relat_1(A_91), k1_relat_1(B_92)) | ~r1_tarski(A_91, B_92) | ~v1_relat_1(B_92) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.71/3.51  tff(c_517, plain, (![A_91, A_17, B_18]: (r1_tarski(k1_relat_1(A_91), A_17) | ~r1_tarski(A_91, k2_zfmisc_1(A_17, B_18)) | ~v1_relat_1(k2_zfmisc_1(A_17, B_18)) | ~v1_relat_1(A_91) | k1_xboole_0=B_18 | k1_xboole_0=A_17)), inference(superposition, [status(thm), theory('equality')], [c_30, c_508])).
% 9.71/3.51  tff(c_5350, plain, (![A_1442, A_1443, B_1444]: (r1_tarski(k1_relat_1(A_1442), A_1443) | ~r1_tarski(A_1442, k2_zfmisc_1(A_1443, B_1444)) | ~v1_relat_1(A_1442) | k1_xboole_0=B_1444 | k1_xboole_0=A_1443)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_517])).
% 9.71/3.51  tff(c_5360, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_582, c_5350])).
% 9.71/3.51  tff(c_5374, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5360])).
% 9.71/3.51  tff(c_5375, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_5328, c_5374])).
% 9.71/3.51  tff(c_5386, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5375])).
% 9.71/3.51  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.71/3.51  tff(c_5488, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5386, c_8])).
% 9.71/3.51  tff(c_5490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_256, c_5488])).
% 9.71/3.51  tff(c_5492, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_5375])).
% 9.71/3.51  tff(c_399, plain, (![C_70, A_71, B_72]: (v1_funct_2(C_70, A_71, B_72) | ~r2_hidden(C_70, k1_funct_2(A_71, B_72)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.71/3.51  tff(c_417, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_399])).
% 9.71/3.51  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.71/3.51  tff(c_1449, plain, (![A_118, B_119, C_120]: (k1_relset_1(A_118, B_119, C_120)=k1_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.71/3.51  tff(c_1590, plain, (![A_139, B_140, A_141]: (k1_relset_1(A_139, B_140, A_141)=k1_relat_1(A_141) | ~r1_tarski(A_141, k2_zfmisc_1(A_139, B_140)))), inference(resolution, [status(thm)], [c_24, c_1449])).
% 9.71/3.51  tff(c_1608, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_582, c_1590])).
% 9.71/3.51  tff(c_2431, plain, (![B_1340, A_1341, C_1342]: (k1_xboole_0=B_1340 | k1_relset_1(A_1341, B_1340, C_1342)=A_1341 | ~v1_funct_2(C_1342, A_1341, B_1340) | ~m1_subset_1(C_1342, k1_zfmisc_1(k2_zfmisc_1(A_1341, B_1340))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.71/3.51  tff(c_9054, plain, (![B_1469, A_1470, A_1471]: (k1_xboole_0=B_1469 | k1_relset_1(A_1470, B_1469, A_1471)=A_1470 | ~v1_funct_2(A_1471, A_1470, B_1469) | ~r1_tarski(A_1471, k2_zfmisc_1(A_1470, B_1469)))), inference(resolution, [status(thm)], [c_24, c_2431])).
% 9.71/3.51  tff(c_9075, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_582, c_9054])).
% 9.71/3.51  tff(c_9094, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_417, c_1608, c_9075])).
% 9.71/3.51  tff(c_9096, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_5492, c_9094])).
% 9.71/3.51  tff(c_9098, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_251])).
% 9.71/3.51  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.71/3.51  tff(c_9106, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_9098, c_10])).
% 9.71/3.51  tff(c_9097, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_251])).
% 9.71/3.51  tff(c_9102, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_9097, c_10])).
% 9.71/3.51  tff(c_9122, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9106, c_9102])).
% 9.71/3.51  tff(c_9107, plain, (![A_55]: (k2_xboole_0(A_55, '#skF_2')=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_9102, c_190])).
% 9.71/3.51  tff(c_9245, plain, (![A_55]: (k2_xboole_0(A_55, '#skF_3')=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_9122, c_9107])).
% 9.71/3.51  tff(c_9131, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9122, c_66])).
% 9.71/3.51  tff(c_18, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.71/3.51  tff(c_9110, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9102, c_9102, c_18])).
% 9.71/3.51  tff(c_9186, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9122, c_9122, c_9110])).
% 9.71/3.51  tff(c_9791, plain, (![C_1505, A_1506, B_1507]: (m1_subset_1(C_1505, k1_zfmisc_1(k2_zfmisc_1(A_1506, B_1507))) | ~r2_hidden(C_1505, k1_funct_2(A_1506, B_1507)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.71/3.51  tff(c_9818, plain, (![C_1511, A_1512]: (m1_subset_1(C_1511, k1_zfmisc_1('#skF_3')) | ~r2_hidden(C_1511, k1_funct_2(A_1512, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_9186, c_9791])).
% 9.71/3.51  tff(c_9844, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_9131, c_9818])).
% 9.71/3.51  tff(c_9849, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_9844, c_22])).
% 9.71/3.51  tff(c_9852, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_9849, c_12])).
% 9.71/3.51  tff(c_9854, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9245, c_9852])).
% 9.71/3.51  tff(c_9115, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9102, c_9102, c_38])).
% 9.71/3.51  tff(c_9143, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9122, c_9122, c_9115])).
% 9.71/3.51  tff(c_9891, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9854, c_9854, c_9143])).
% 9.71/3.51  tff(c_9129, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9122, c_173])).
% 9.71/3.51  tff(c_9888, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9854, c_9129])).
% 9.71/3.51  tff(c_9957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9891, c_9888])).
% 9.71/3.51  tff(c_9958, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_64])).
% 9.71/3.51  tff(c_10232, plain, (![C_1545, A_1546, B_1547]: (m1_subset_1(C_1545, k1_zfmisc_1(k2_zfmisc_1(A_1546, B_1547))) | ~r2_hidden(C_1545, k1_funct_2(A_1546, B_1547)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.71/3.51  tff(c_13840, plain, (![C_1723, A_1724, B_1725]: (r1_tarski(C_1723, k2_zfmisc_1(A_1724, B_1725)) | ~r2_hidden(C_1723, k1_funct_2(A_1724, B_1725)))), inference(resolution, [status(thm)], [c_10232, c_22])).
% 9.71/3.51  tff(c_13861, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_66, c_13840])).
% 9.71/3.51  tff(c_13866, plain, (![A_1726, B_1727]: (r1_tarski(k2_relat_1(A_1726), k2_relat_1(B_1727)) | ~r1_tarski(A_1726, B_1727) | ~v1_relat_1(B_1727) | ~v1_relat_1(A_1726))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.71/3.51  tff(c_13875, plain, (![A_1726, B_18, A_17]: (r1_tarski(k2_relat_1(A_1726), B_18) | ~r1_tarski(A_1726, k2_zfmisc_1(A_17, B_18)) | ~v1_relat_1(k2_zfmisc_1(A_17, B_18)) | ~v1_relat_1(A_1726) | k1_xboole_0=B_18 | k1_xboole_0=A_17)), inference(superposition, [status(thm), theory('equality')], [c_28, c_13866])).
% 9.71/3.51  tff(c_17211, plain, (![A_3187, B_3188, A_3189]: (r1_tarski(k2_relat_1(A_3187), B_3188) | ~r1_tarski(A_3187, k2_zfmisc_1(A_3189, B_3188)) | ~v1_relat_1(A_3187) | k1_xboole_0=B_3188 | k1_xboole_0=A_3189)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_13875])).
% 9.71/3.51  tff(c_17219, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_13861, c_17211])).
% 9.71/3.51  tff(c_17232, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_17219])).
% 9.71/3.51  tff(c_17233, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_9958, c_17232])).
% 9.71/3.51  tff(c_17238, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_17233])).
% 9.71/3.51  tff(c_112, plain, (![A_39, B_40]: (v1_relat_1(k2_zfmisc_1(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.71/3.51  tff(c_114, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_112])).
% 9.71/3.51  tff(c_9959, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 9.71/3.51  tff(c_10287, plain, (![A_1553, B_1554]: (r1_tarski(k1_relat_1(A_1553), k1_relat_1(B_1554)) | ~r1_tarski(A_1553, B_1554) | ~v1_relat_1(B_1554) | ~v1_relat_1(A_1553))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.71/3.51  tff(c_10299, plain, (![B_1554]: (r1_tarski('#skF_2', k1_relat_1(B_1554)) | ~r1_tarski('#skF_4', B_1554) | ~v1_relat_1(B_1554) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9959, c_10287])).
% 9.71/3.51  tff(c_10332, plain, (![B_1557]: (r1_tarski('#skF_2', k1_relat_1(B_1557)) | ~r1_tarski('#skF_4', B_1557) | ~v1_relat_1(B_1557))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_10299])).
% 9.71/3.51  tff(c_10344, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_4', k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_10332])).
% 9.71/3.51  tff(c_10351, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_10344])).
% 9.71/3.51  tff(c_13781, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_10351])).
% 9.71/3.51  tff(c_17303, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17238, c_13781])).
% 9.71/3.51  tff(c_17327, plain, (![B_12]: (k2_zfmisc_1('#skF_2', B_12)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17238, c_17238, c_20])).
% 9.71/3.51  tff(c_17498, plain, (r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17327, c_13861])).
% 9.71/3.51  tff(c_17500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17303, c_17498])).
% 9.71/3.51  tff(c_17501, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_17233])).
% 9.71/3.51  tff(c_17596, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17501, c_8])).
% 9.71/3.51  tff(c_17598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10006, c_17596])).
% 9.71/3.51  tff(c_17599, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_10351])).
% 9.71/3.51  tff(c_17603, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_17599, c_12])).
% 9.71/3.52  tff(c_17605, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10003, c_17603])).
% 9.71/3.52  tff(c_17626, plain, (![A_1]: (k2_xboole_0(A_1, '#skF_2')=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_17605, c_10003])).
% 9.71/3.52  tff(c_17600, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_10351])).
% 9.71/3.52  tff(c_17652, plain, (r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17605, c_17600])).
% 9.71/3.52  tff(c_17656, plain, (k2_xboole_0('#skF_4', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_17652, c_12])).
% 9.71/3.52  tff(c_17882, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17626, c_17656])).
% 9.71/3.52  tff(c_17633, plain, (![A_10]: (r1_tarski('#skF_2', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_17605, c_14])).
% 9.71/3.52  tff(c_17894, plain, (![A_10]: (r1_tarski('#skF_4', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_17882, c_17633])).
% 9.71/3.52  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.71/3.52  tff(c_17634, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_17605, c_17605, c_36])).
% 9.71/3.52  tff(c_17893, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17882, c_17882, c_17634])).
% 9.71/3.52  tff(c_17955, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17893, c_9958])).
% 9.71/3.52  tff(c_17958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17894, c_17955])).
% 9.71/3.52  tff(c_17960, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_9981])).
% 9.71/3.52  tff(c_17968, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_17960, c_10])).
% 9.71/3.52  tff(c_9989, plain, (![A_1523]: (k2_xboole_0(A_1523, k1_xboole_0)=A_1523)), inference(superposition, [status(thm), theory('equality')], [c_9983, c_2])).
% 9.71/3.52  tff(c_18029, plain, (![A_1523]: (k2_xboole_0(A_1523, '#skF_3')=A_1523)), inference(demodulation, [status(thm), theory('equality')], [c_17968, c_9989])).
% 9.71/3.52  tff(c_17959, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_9981])).
% 9.71/3.52  tff(c_17964, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_17959, c_10])).
% 9.71/3.52  tff(c_17983, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17968, c_17964])).
% 9.71/3.52  tff(c_17992, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_17983, c_66])).
% 9.71/3.52  tff(c_17972, plain, (![B_12]: (k2_zfmisc_1('#skF_2', B_12)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17964, c_17964, c_20])).
% 9.71/3.52  tff(c_18134, plain, (![B_12]: (k2_zfmisc_1('#skF_3', B_12)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17983, c_17983, c_17972])).
% 9.71/3.52  tff(c_18426, plain, (![C_3243, A_3244, B_3245]: (m1_subset_1(C_3243, k1_zfmisc_1(k2_zfmisc_1(A_3244, B_3245))) | ~r2_hidden(C_3243, k1_funct_2(A_3244, B_3245)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.71/3.52  tff(c_18438, plain, (![C_3247, B_3248]: (m1_subset_1(C_3247, k1_zfmisc_1('#skF_3')) | ~r2_hidden(C_3247, k1_funct_2('#skF_3', B_3248)))), inference(superposition, [status(thm), theory('equality')], [c_18134, c_18426])).
% 9.71/3.52  tff(c_18458, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_17992, c_18438])).
% 9.71/3.52  tff(c_18463, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_18458, c_22])).
% 9.71/3.52  tff(c_18466, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_18463, c_12])).
% 9.71/3.52  tff(c_18468, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18029, c_18466])).
% 9.71/3.52  tff(c_17974, plain, (![A_10]: (r1_tarski('#skF_2', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_17964, c_14])).
% 9.71/3.52  tff(c_18005, plain, (![A_10]: (r1_tarski('#skF_3', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_17983, c_17974])).
% 9.71/3.52  tff(c_18496, plain, (![A_10]: (r1_tarski('#skF_4', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_18468, c_18005])).
% 9.71/3.52  tff(c_17975, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_17964, c_17964, c_36])).
% 9.71/3.52  tff(c_18015, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17983, c_17983, c_17975])).
% 9.71/3.52  tff(c_18494, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18468, c_18468, c_18015])).
% 9.71/3.52  tff(c_18503, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18468, c_9958])).
% 9.71/3.52  tff(c_18547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18496, c_18494, c_18503])).
% 9.71/3.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.71/3.52  
% 9.71/3.52  Inference rules
% 9.71/3.52  ----------------------
% 9.71/3.52  #Ref     : 0
% 9.71/3.52  #Sup     : 4033
% 9.71/3.52  #Fact    : 22
% 9.71/3.52  #Define  : 0
% 9.71/3.52  #Split   : 29
% 9.71/3.52  #Chain   : 0
% 9.71/3.52  #Close   : 0
% 9.71/3.52  
% 9.71/3.52  Ordering : KBO
% 9.71/3.52  
% 9.71/3.52  Simplification rules
% 9.71/3.52  ----------------------
% 9.71/3.52  #Subsume      : 964
% 9.71/3.52  #Demod        : 4002
% 9.71/3.52  #Tautology    : 2068
% 9.71/3.52  #SimpNegUnit  : 194
% 9.71/3.52  #BackRed      : 804
% 9.71/3.52  
% 9.71/3.52  #Partial instantiations: 390
% 9.71/3.52  #Strategies tried      : 1
% 9.71/3.52  
% 9.71/3.52  Timing (in seconds)
% 9.71/3.52  ----------------------
% 9.81/3.52  Preprocessing        : 0.34
% 9.81/3.52  Parsing              : 0.18
% 9.81/3.52  CNF conversion       : 0.02
% 9.81/3.52  Main loop            : 2.37
% 9.81/3.52  Inferencing          : 0.73
% 9.81/3.52  Reduction            : 0.77
% 9.81/3.52  Demodulation         : 0.54
% 9.81/3.52  BG Simplification    : 0.08
% 9.81/3.52  Subsumption          : 0.63
% 9.81/3.52  Abstraction          : 0.09
% 9.81/3.52  MUC search           : 0.00
% 9.81/3.52  Cooper               : 0.00
% 9.81/3.52  Total                : 2.77
% 9.81/3.52  Index Insertion      : 0.00
% 9.81/3.52  Index Deletion       : 0.00
% 9.81/3.52  Index Matching       : 0.00
% 9.81/3.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
