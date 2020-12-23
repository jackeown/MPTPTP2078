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
% DateTime   : Thu Dec  3 10:28:16 EST 2020

% Result     : Theorem 8.04s
% Output     : CNFRefutation 8.04s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 864 expanded)
%              Number of leaves         :   34 ( 306 expanded)
%              Depth                    :   22
%              Number of atoms          :  210 (2007 expanded)
%              Number of equality atoms :   78 ( 724 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_97,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_44,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_70,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_80,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

tff(c_52,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_54,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_212,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_216,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_212])).

tff(c_223,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_216])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_56,plain,(
    v1_zfmisc_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_48,plain,(
    ! [A_30] :
      ( k6_domain_1(A_30,'#skF_5'(A_30)) = A_30
      | ~ v1_zfmisc_1(A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_50,plain,(
    ! [A_30] :
      ( m1_subset_1('#skF_5'(A_30),A_30)
      | ~ v1_zfmisc_1(A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_305,plain,(
    ! [A_77,B_78] :
      ( k6_domain_1(A_77,B_78) = k1_tarski(B_78)
      | ~ m1_subset_1(B_78,A_77)
      | v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2255,plain,(
    ! [A_1571] :
      ( k6_domain_1(A_1571,'#skF_5'(A_1571)) = k1_tarski('#skF_5'(A_1571))
      | ~ v1_zfmisc_1(A_1571)
      | v1_xboole_0(A_1571) ) ),
    inference(resolution,[status(thm)],[c_50,c_305])).

tff(c_3635,plain,(
    ! [A_2430] :
      ( k1_tarski('#skF_5'(A_2430)) = A_2430
      | ~ v1_zfmisc_1(A_2430)
      | v1_xboole_0(A_2430)
      | ~ v1_zfmisc_1(A_2430)
      | v1_xboole_0(A_2430) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2255])).

tff(c_16,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_82,plain,(
    ! [A_39,B_40] : k2_xboole_0(k1_tarski(A_39),B_40) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_86,plain,(
    ! [A_39] : k1_tarski(A_39) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_82])).

tff(c_42,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_4'(A_26),A_26)
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_90,plain,(
    ! [C_44,A_45] :
      ( C_44 = A_45
      | ~ r2_hidden(C_44,k1_tarski(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_94,plain,(
    ! [A_45] :
      ( '#skF_4'(k1_tarski(A_45)) = A_45
      | k1_tarski(A_45) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_90])).

tff(c_100,plain,(
    ! [A_45] : '#skF_4'(k1_tarski(A_45)) = A_45 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_94])).

tff(c_4394,plain,(
    ! [A_2821] :
      ( '#skF_5'(A_2821) = '#skF_4'(A_2821)
      | ~ v1_zfmisc_1(A_2821)
      | v1_xboole_0(A_2821)
      | ~ v1_zfmisc_1(A_2821)
      | v1_xboole_0(A_2821) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3635,c_100])).

tff(c_4396,plain,
    ( '#skF_5'('#skF_7') = '#skF_4'('#skF_7')
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_4394])).

tff(c_4399,plain,
    ( '#skF_5'('#skF_7') = '#skF_4'('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4396])).

tff(c_4400,plain,(
    '#skF_5'('#skF_7') = '#skF_4'('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4399])).

tff(c_2283,plain,(
    ! [A_30] :
      ( k1_tarski('#skF_5'(A_30)) = A_30
      | ~ v1_zfmisc_1(A_30)
      | v1_xboole_0(A_30)
      | ~ v1_zfmisc_1(A_30)
      | v1_xboole_0(A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2255])).

tff(c_4410,plain,
    ( k1_tarski('#skF_4'('#skF_7')) = '#skF_7'
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7')
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4400,c_2283])).

tff(c_4429,plain,
    ( k1_tarski('#skF_4'('#skF_7')) = '#skF_7'
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_4410])).

tff(c_4430,plain,(
    k1_tarski('#skF_4'('#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4429])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_224,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),A_60)
      | r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_264,plain,(
    ! [A_71,B_72] :
      ( '#skF_1'(k1_tarski(A_71),B_72) = A_71
      | r1_tarski(k1_tarski(A_71),B_72) ) ),
    inference(resolution,[status(thm)],[c_224,c_20])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_352,plain,(
    ! [A_83,B_84] :
      ( k2_xboole_0(k1_tarski(A_83),B_84) = B_84
      | '#skF_1'(k1_tarski(A_83),B_84) = A_83 ) ),
    inference(resolution,[status(thm)],[c_264,c_14])).

tff(c_38,plain,(
    ! [A_24,B_25] : k2_xboole_0(k1_tarski(A_24),B_25) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_416,plain,(
    ! [B_88,A_89] :
      ( k1_xboole_0 != B_88
      | '#skF_1'(k1_tarski(A_89),B_88) = A_89 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_38])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_647,plain,(
    ! [A_107,B_108] :
      ( ~ r2_hidden(A_107,B_108)
      | r1_tarski(k1_tarski(A_107),B_108)
      | k1_xboole_0 != B_108 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_4])).

tff(c_694,plain,(
    ! [A_112,B_113] :
      ( k2_xboole_0(k1_tarski(A_112),B_113) = B_113
      | ~ r2_hidden(A_112,B_113)
      | k1_xboole_0 != B_113 ) ),
    inference(resolution,[status(thm)],[c_647,c_14])).

tff(c_736,plain,(
    ! [B_114,A_115] :
      ( k1_xboole_0 != B_114
      | ~ r2_hidden(A_115,B_114)
      | k1_xboole_0 != B_114 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_694,c_38])).

tff(c_759,plain,(
    ! [A_116,B_117] :
      ( k1_xboole_0 != A_116
      | r1_tarski(A_116,B_117) ) ),
    inference(resolution,[status(thm)],[c_6,c_736])).

tff(c_103,plain,(
    ! [A_46] : '#skF_4'(k1_tarski(A_46)) = A_46 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_94])).

tff(c_40,plain,(
    ! [A_26] :
      ( r1_xboole_0('#skF_4'(A_26),A_26)
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_112,plain,(
    ! [A_46] :
      ( r1_xboole_0(A_46,k1_tarski(A_46))
      | k1_tarski(A_46) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_40])).

tff(c_119,plain,(
    ! [A_46] : r1_xboole_0(A_46,k1_tarski(A_46)) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_112])).

tff(c_544,plain,(
    ! [A_97,B_98,C_99] :
      ( ~ r1_xboole_0(A_97,B_98)
      | ~ r1_tarski(C_99,B_98)
      | ~ r1_tarski(C_99,A_97)
      | v1_xboole_0(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_549,plain,(
    ! [C_99,A_46] :
      ( ~ r1_tarski(C_99,k1_tarski(A_46))
      | ~ r1_tarski(C_99,A_46)
      | v1_xboole_0(C_99) ) ),
    inference(resolution,[status(thm)],[c_119,c_544])).

tff(c_894,plain,(
    ! [A_124,A_125] :
      ( ~ r1_tarski(A_124,A_125)
      | v1_xboole_0(A_124)
      | k1_xboole_0 != A_124 ) ),
    inference(resolution,[status(thm)],[c_759,c_549])).

tff(c_909,plain,
    ( v1_xboole_0('#skF_6')
    | k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_54,c_894])).

tff(c_916,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_909])).

tff(c_229,plain,(
    ! [A_14,B_61] :
      ( '#skF_1'(k1_tarski(A_14),B_61) = A_14
      | r1_tarski(k1_tarski(A_14),B_61) ) ),
    inference(resolution,[status(thm)],[c_224,c_20])).

tff(c_238,plain,(
    ! [C_65,B_66,A_67] :
      ( r2_hidden(C_65,B_66)
      | ~ r2_hidden(C_65,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_292,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_4'(A_75),B_76)
      | ~ r1_tarski(A_75,B_76)
      | k1_xboole_0 = A_75 ) ),
    inference(resolution,[status(thm)],[c_42,c_238])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2485,plain,(
    ! [A_1742,B_1743,B_1744] :
      ( r2_hidden('#skF_4'(A_1742),B_1743)
      | ~ r1_tarski(B_1744,B_1743)
      | ~ r1_tarski(A_1742,B_1744)
      | k1_xboole_0 = A_1742 ) ),
    inference(resolution,[status(thm)],[c_292,c_2])).

tff(c_2501,plain,(
    ! [A_1764] :
      ( r2_hidden('#skF_4'(A_1764),'#skF_7')
      | ~ r1_tarski(A_1764,'#skF_6')
      | k1_xboole_0 = A_1764 ) ),
    inference(resolution,[status(thm)],[c_54,c_2485])).

tff(c_2512,plain,(
    ! [A_45] :
      ( r2_hidden(A_45,'#skF_7')
      | ~ r1_tarski(k1_tarski(A_45),'#skF_6')
      | k1_tarski(A_45) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_2501])).

tff(c_2623,plain,(
    ! [A_1805] :
      ( r2_hidden(A_1805,'#skF_7')
      | ~ r1_tarski(k1_tarski(A_1805),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_2512])).

tff(c_2642,plain,(
    ! [A_1825] :
      ( r2_hidden(A_1825,'#skF_7')
      | '#skF_1'(k1_tarski(A_1825),'#skF_6') = A_1825 ) ),
    inference(resolution,[status(thm)],[c_229,c_2623])).

tff(c_2721,plain,(
    ! [A_1845] :
      ( ~ r2_hidden(A_1845,'#skF_6')
      | r1_tarski(k1_tarski(A_1845),'#skF_6')
      | r2_hidden(A_1845,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2642,c_4])).

tff(c_2516,plain,(
    ! [A_45] :
      ( r2_hidden(A_45,'#skF_7')
      | ~ r1_tarski(k1_tarski(A_45),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_2512])).

tff(c_2833,plain,(
    ! [A_1886] :
      ( ~ r2_hidden(A_1886,'#skF_6')
      | r2_hidden(A_1886,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2721,c_2516])).

tff(c_3193,plain,(
    ! [A_2184,B_2185] :
      ( r2_hidden(A_2184,B_2185)
      | ~ r1_tarski('#skF_7',B_2185)
      | ~ r2_hidden(A_2184,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2833,c_2])).

tff(c_3217,plain,(
    ! [B_2185] :
      ( r2_hidden('#skF_4'('#skF_6'),B_2185)
      | ~ r1_tarski('#skF_7',B_2185)
      | k1_xboole_0 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_42,c_3193])).

tff(c_3228,plain,(
    ! [B_2205] :
      ( r2_hidden('#skF_4'('#skF_6'),B_2205)
      | ~ r1_tarski('#skF_7',B_2205) ) ),
    inference(negUnitSimplification,[status(thm)],[c_916,c_3217])).

tff(c_3256,plain,(
    ! [A_14] :
      ( A_14 = '#skF_4'('#skF_6')
      | ~ r1_tarski('#skF_7',k1_tarski(A_14)) ) ),
    inference(resolution,[status(thm)],[c_3228,c_20])).

tff(c_4484,plain,
    ( '#skF_4'('#skF_7') = '#skF_4'('#skF_6')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4430,c_3256])).

tff(c_4634,plain,(
    '#skF_4'('#skF_7') = '#skF_4'('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4484])).

tff(c_361,plain,(
    ! [B_84,A_83] :
      ( k1_xboole_0 != B_84
      | '#skF_1'(k1_tarski(A_83),B_84) = A_83 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_38])).

tff(c_4537,plain,(
    ! [B_84] :
      ( k1_xboole_0 != B_84
      | '#skF_4'('#skF_7') = '#skF_1'('#skF_7',B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4430,c_361])).

tff(c_5427,plain,(
    '#skF_4'('#skF_6') = '#skF_1'('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4634,c_4537])).

tff(c_5444,plain,(
    '#skF_4'('#skF_7') = '#skF_1'('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5427,c_4634])).

tff(c_4555,plain,(
    ! [B_61] :
      ( '#skF_1'(k1_tarski('#skF_4'('#skF_7')),B_61) = '#skF_4'('#skF_7')
      | r1_tarski('#skF_7',B_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4430,c_229])).

tff(c_4652,plain,(
    ! [B_61] :
      ( '#skF_4'('#skF_7') = '#skF_1'('#skF_7',B_61)
      | r1_tarski('#skF_7',B_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4430,c_4555])).

tff(c_9545,plain,(
    ! [B_7347] :
      ( '#skF_1'('#skF_7',k1_xboole_0) = '#skF_1'('#skF_7',B_7347)
      | r1_tarski('#skF_7',B_7347) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5444,c_4652])).

tff(c_9751,plain,(
    '#skF_1'('#skF_7',k1_xboole_0) = '#skF_1'('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_9545,c_223])).

tff(c_5449,plain,(
    ! [B_3404] :
      ( k1_xboole_0 != B_3404
      | '#skF_4'('#skF_6') = '#skF_1'('#skF_7',B_3404) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4634,c_4537])).

tff(c_5491,plain,(
    ! [B_3404] :
      ( r2_hidden('#skF_1'('#skF_7',B_3404),'#skF_6')
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 != B_3404 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5449,c_42])).

tff(c_5521,plain,(
    ! [B_3404] :
      ( r2_hidden('#skF_1'('#skF_7',B_3404),'#skF_6')
      | k1_xboole_0 != B_3404 ) ),
    inference(negUnitSimplification,[status(thm)],[c_916,c_5491])).

tff(c_9855,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9751,c_5521])).

tff(c_11008,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_9855,c_4])).

tff(c_11032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_11008])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:53:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.04/2.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.04/2.79  
% 8.04/2.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.04/2.80  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1
% 8.04/2.80  
% 8.04/2.80  %Foreground sorts:
% 8.04/2.80  
% 8.04/2.80  
% 8.04/2.80  %Background operators:
% 8.04/2.80  
% 8.04/2.80  
% 8.04/2.80  %Foreground operators:
% 8.04/2.80  tff('#skF_5', type, '#skF_5': $i > $i).
% 8.04/2.80  tff('#skF_4', type, '#skF_4': $i > $i).
% 8.04/2.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.04/2.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.04/2.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.04/2.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.04/2.80  tff('#skF_7', type, '#skF_7': $i).
% 8.04/2.80  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.04/2.80  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 8.04/2.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.04/2.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.04/2.80  tff('#skF_6', type, '#skF_6': $i).
% 8.04/2.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.04/2.80  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.04/2.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.04/2.80  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.04/2.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.04/2.80  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.04/2.80  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 8.04/2.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.04/2.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.04/2.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.04/2.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.04/2.80  
% 8.04/2.82  tff(f_111, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 8.04/2.82  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.04/2.82  tff(f_97, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 8.04/2.82  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 8.04/2.82  tff(f_44, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.04/2.82  tff(f_70, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 8.04/2.82  tff(f_80, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 8.04/2.82  tff(f_61, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 8.04/2.82  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.04/2.82  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.04/2.82  tff(f_54, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_xboole_1)).
% 8.04/2.82  tff(c_52, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.04/2.82  tff(c_54, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.04/2.82  tff(c_212, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.04/2.82  tff(c_216, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_212])).
% 8.04/2.82  tff(c_223, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_52, c_216])).
% 8.04/2.82  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.04/2.82  tff(c_58, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.04/2.82  tff(c_56, plain, (v1_zfmisc_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.04/2.82  tff(c_48, plain, (![A_30]: (k6_domain_1(A_30, '#skF_5'(A_30))=A_30 | ~v1_zfmisc_1(A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.04/2.82  tff(c_50, plain, (![A_30]: (m1_subset_1('#skF_5'(A_30), A_30) | ~v1_zfmisc_1(A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.04/2.82  tff(c_305, plain, (![A_77, B_78]: (k6_domain_1(A_77, B_78)=k1_tarski(B_78) | ~m1_subset_1(B_78, A_77) | v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.04/2.82  tff(c_2255, plain, (![A_1571]: (k6_domain_1(A_1571, '#skF_5'(A_1571))=k1_tarski('#skF_5'(A_1571)) | ~v1_zfmisc_1(A_1571) | v1_xboole_0(A_1571))), inference(resolution, [status(thm)], [c_50, c_305])).
% 8.04/2.82  tff(c_3635, plain, (![A_2430]: (k1_tarski('#skF_5'(A_2430))=A_2430 | ~v1_zfmisc_1(A_2430) | v1_xboole_0(A_2430) | ~v1_zfmisc_1(A_2430) | v1_xboole_0(A_2430))), inference(superposition, [status(thm), theory('equality')], [c_48, c_2255])).
% 8.04/2.82  tff(c_16, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.04/2.82  tff(c_82, plain, (![A_39, B_40]: (k2_xboole_0(k1_tarski(A_39), B_40)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.04/2.82  tff(c_86, plain, (![A_39]: (k1_tarski(A_39)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_82])).
% 8.04/2.82  tff(c_42, plain, (![A_26]: (r2_hidden('#skF_4'(A_26), A_26) | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.04/2.82  tff(c_90, plain, (![C_44, A_45]: (C_44=A_45 | ~r2_hidden(C_44, k1_tarski(A_45)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.04/2.82  tff(c_94, plain, (![A_45]: ('#skF_4'(k1_tarski(A_45))=A_45 | k1_tarski(A_45)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_90])).
% 8.04/2.82  tff(c_100, plain, (![A_45]: ('#skF_4'(k1_tarski(A_45))=A_45)), inference(negUnitSimplification, [status(thm)], [c_86, c_94])).
% 8.04/2.82  tff(c_4394, plain, (![A_2821]: ('#skF_5'(A_2821)='#skF_4'(A_2821) | ~v1_zfmisc_1(A_2821) | v1_xboole_0(A_2821) | ~v1_zfmisc_1(A_2821) | v1_xboole_0(A_2821))), inference(superposition, [status(thm), theory('equality')], [c_3635, c_100])).
% 8.04/2.82  tff(c_4396, plain, ('#skF_5'('#skF_7')='#skF_4'('#skF_7') | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_56, c_4394])).
% 8.04/2.82  tff(c_4399, plain, ('#skF_5'('#skF_7')='#skF_4'('#skF_7') | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4396])).
% 8.04/2.82  tff(c_4400, plain, ('#skF_5'('#skF_7')='#skF_4'('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_58, c_4399])).
% 8.04/2.82  tff(c_2283, plain, (![A_30]: (k1_tarski('#skF_5'(A_30))=A_30 | ~v1_zfmisc_1(A_30) | v1_xboole_0(A_30) | ~v1_zfmisc_1(A_30) | v1_xboole_0(A_30))), inference(superposition, [status(thm), theory('equality')], [c_48, c_2255])).
% 8.04/2.82  tff(c_4410, plain, (k1_tarski('#skF_4'('#skF_7'))='#skF_7' | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7') | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4400, c_2283])).
% 8.04/2.82  tff(c_4429, plain, (k1_tarski('#skF_4'('#skF_7'))='#skF_7' | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_4410])).
% 8.04/2.82  tff(c_4430, plain, (k1_tarski('#skF_4'('#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_58, c_4429])).
% 8.04/2.82  tff(c_60, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.04/2.82  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.04/2.82  tff(c_224, plain, (![A_60, B_61]: (r2_hidden('#skF_1'(A_60, B_61), A_60) | r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.04/2.82  tff(c_20, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.04/2.82  tff(c_264, plain, (![A_71, B_72]: ('#skF_1'(k1_tarski(A_71), B_72)=A_71 | r1_tarski(k1_tarski(A_71), B_72))), inference(resolution, [status(thm)], [c_224, c_20])).
% 8.04/2.82  tff(c_14, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.04/2.82  tff(c_352, plain, (![A_83, B_84]: (k2_xboole_0(k1_tarski(A_83), B_84)=B_84 | '#skF_1'(k1_tarski(A_83), B_84)=A_83)), inference(resolution, [status(thm)], [c_264, c_14])).
% 8.04/2.82  tff(c_38, plain, (![A_24, B_25]: (k2_xboole_0(k1_tarski(A_24), B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.04/2.82  tff(c_416, plain, (![B_88, A_89]: (k1_xboole_0!=B_88 | '#skF_1'(k1_tarski(A_89), B_88)=A_89)), inference(superposition, [status(thm), theory('equality')], [c_352, c_38])).
% 8.04/2.82  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.04/2.82  tff(c_647, plain, (![A_107, B_108]: (~r2_hidden(A_107, B_108) | r1_tarski(k1_tarski(A_107), B_108) | k1_xboole_0!=B_108)), inference(superposition, [status(thm), theory('equality')], [c_416, c_4])).
% 8.04/2.82  tff(c_694, plain, (![A_112, B_113]: (k2_xboole_0(k1_tarski(A_112), B_113)=B_113 | ~r2_hidden(A_112, B_113) | k1_xboole_0!=B_113)), inference(resolution, [status(thm)], [c_647, c_14])).
% 8.04/2.82  tff(c_736, plain, (![B_114, A_115]: (k1_xboole_0!=B_114 | ~r2_hidden(A_115, B_114) | k1_xboole_0!=B_114)), inference(superposition, [status(thm), theory('equality')], [c_694, c_38])).
% 8.04/2.82  tff(c_759, plain, (![A_116, B_117]: (k1_xboole_0!=A_116 | r1_tarski(A_116, B_117))), inference(resolution, [status(thm)], [c_6, c_736])).
% 8.04/2.82  tff(c_103, plain, (![A_46]: ('#skF_4'(k1_tarski(A_46))=A_46)), inference(negUnitSimplification, [status(thm)], [c_86, c_94])).
% 8.04/2.82  tff(c_40, plain, (![A_26]: (r1_xboole_0('#skF_4'(A_26), A_26) | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.04/2.82  tff(c_112, plain, (![A_46]: (r1_xboole_0(A_46, k1_tarski(A_46)) | k1_tarski(A_46)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_103, c_40])).
% 8.04/2.82  tff(c_119, plain, (![A_46]: (r1_xboole_0(A_46, k1_tarski(A_46)))), inference(negUnitSimplification, [status(thm)], [c_86, c_112])).
% 8.04/2.82  tff(c_544, plain, (![A_97, B_98, C_99]: (~r1_xboole_0(A_97, B_98) | ~r1_tarski(C_99, B_98) | ~r1_tarski(C_99, A_97) | v1_xboole_0(C_99))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.04/2.82  tff(c_549, plain, (![C_99, A_46]: (~r1_tarski(C_99, k1_tarski(A_46)) | ~r1_tarski(C_99, A_46) | v1_xboole_0(C_99))), inference(resolution, [status(thm)], [c_119, c_544])).
% 8.04/2.82  tff(c_894, plain, (![A_124, A_125]: (~r1_tarski(A_124, A_125) | v1_xboole_0(A_124) | k1_xboole_0!=A_124)), inference(resolution, [status(thm)], [c_759, c_549])).
% 8.04/2.82  tff(c_909, plain, (v1_xboole_0('#skF_6') | k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_54, c_894])).
% 8.04/2.82  tff(c_916, plain, (k1_xboole_0!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_60, c_909])).
% 8.04/2.82  tff(c_229, plain, (![A_14, B_61]: ('#skF_1'(k1_tarski(A_14), B_61)=A_14 | r1_tarski(k1_tarski(A_14), B_61))), inference(resolution, [status(thm)], [c_224, c_20])).
% 8.04/2.82  tff(c_238, plain, (![C_65, B_66, A_67]: (r2_hidden(C_65, B_66) | ~r2_hidden(C_65, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.04/2.82  tff(c_292, plain, (![A_75, B_76]: (r2_hidden('#skF_4'(A_75), B_76) | ~r1_tarski(A_75, B_76) | k1_xboole_0=A_75)), inference(resolution, [status(thm)], [c_42, c_238])).
% 8.04/2.82  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.04/2.82  tff(c_2485, plain, (![A_1742, B_1743, B_1744]: (r2_hidden('#skF_4'(A_1742), B_1743) | ~r1_tarski(B_1744, B_1743) | ~r1_tarski(A_1742, B_1744) | k1_xboole_0=A_1742)), inference(resolution, [status(thm)], [c_292, c_2])).
% 8.04/2.82  tff(c_2501, plain, (![A_1764]: (r2_hidden('#skF_4'(A_1764), '#skF_7') | ~r1_tarski(A_1764, '#skF_6') | k1_xboole_0=A_1764)), inference(resolution, [status(thm)], [c_54, c_2485])).
% 8.04/2.82  tff(c_2512, plain, (![A_45]: (r2_hidden(A_45, '#skF_7') | ~r1_tarski(k1_tarski(A_45), '#skF_6') | k1_tarski(A_45)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_100, c_2501])).
% 8.04/2.82  tff(c_2623, plain, (![A_1805]: (r2_hidden(A_1805, '#skF_7') | ~r1_tarski(k1_tarski(A_1805), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_86, c_2512])).
% 8.04/2.82  tff(c_2642, plain, (![A_1825]: (r2_hidden(A_1825, '#skF_7') | '#skF_1'(k1_tarski(A_1825), '#skF_6')=A_1825)), inference(resolution, [status(thm)], [c_229, c_2623])).
% 8.04/2.82  tff(c_2721, plain, (![A_1845]: (~r2_hidden(A_1845, '#skF_6') | r1_tarski(k1_tarski(A_1845), '#skF_6') | r2_hidden(A_1845, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2642, c_4])).
% 8.04/2.82  tff(c_2516, plain, (![A_45]: (r2_hidden(A_45, '#skF_7') | ~r1_tarski(k1_tarski(A_45), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_86, c_2512])).
% 8.04/2.82  tff(c_2833, plain, (![A_1886]: (~r2_hidden(A_1886, '#skF_6') | r2_hidden(A_1886, '#skF_7'))), inference(resolution, [status(thm)], [c_2721, c_2516])).
% 8.04/2.82  tff(c_3193, plain, (![A_2184, B_2185]: (r2_hidden(A_2184, B_2185) | ~r1_tarski('#skF_7', B_2185) | ~r2_hidden(A_2184, '#skF_6'))), inference(resolution, [status(thm)], [c_2833, c_2])).
% 8.04/2.82  tff(c_3217, plain, (![B_2185]: (r2_hidden('#skF_4'('#skF_6'), B_2185) | ~r1_tarski('#skF_7', B_2185) | k1_xboole_0='#skF_6')), inference(resolution, [status(thm)], [c_42, c_3193])).
% 8.04/2.82  tff(c_3228, plain, (![B_2205]: (r2_hidden('#skF_4'('#skF_6'), B_2205) | ~r1_tarski('#skF_7', B_2205))), inference(negUnitSimplification, [status(thm)], [c_916, c_3217])).
% 8.04/2.82  tff(c_3256, plain, (![A_14]: (A_14='#skF_4'('#skF_6') | ~r1_tarski('#skF_7', k1_tarski(A_14)))), inference(resolution, [status(thm)], [c_3228, c_20])).
% 8.04/2.82  tff(c_4484, plain, ('#skF_4'('#skF_7')='#skF_4'('#skF_6') | ~r1_tarski('#skF_7', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4430, c_3256])).
% 8.04/2.82  tff(c_4634, plain, ('#skF_4'('#skF_7')='#skF_4'('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4484])).
% 8.04/2.82  tff(c_361, plain, (![B_84, A_83]: (k1_xboole_0!=B_84 | '#skF_1'(k1_tarski(A_83), B_84)=A_83)), inference(superposition, [status(thm), theory('equality')], [c_352, c_38])).
% 8.04/2.82  tff(c_4537, plain, (![B_84]: (k1_xboole_0!=B_84 | '#skF_4'('#skF_7')='#skF_1'('#skF_7', B_84))), inference(superposition, [status(thm), theory('equality')], [c_4430, c_361])).
% 8.04/2.82  tff(c_5427, plain, ('#skF_4'('#skF_6')='#skF_1'('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4634, c_4537])).
% 8.04/2.82  tff(c_5444, plain, ('#skF_4'('#skF_7')='#skF_1'('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5427, c_4634])).
% 8.04/2.82  tff(c_4555, plain, (![B_61]: ('#skF_1'(k1_tarski('#skF_4'('#skF_7')), B_61)='#skF_4'('#skF_7') | r1_tarski('#skF_7', B_61))), inference(superposition, [status(thm), theory('equality')], [c_4430, c_229])).
% 8.04/2.82  tff(c_4652, plain, (![B_61]: ('#skF_4'('#skF_7')='#skF_1'('#skF_7', B_61) | r1_tarski('#skF_7', B_61))), inference(demodulation, [status(thm), theory('equality')], [c_4430, c_4555])).
% 8.04/2.82  tff(c_9545, plain, (![B_7347]: ('#skF_1'('#skF_7', k1_xboole_0)='#skF_1'('#skF_7', B_7347) | r1_tarski('#skF_7', B_7347))), inference(demodulation, [status(thm), theory('equality')], [c_5444, c_4652])).
% 8.04/2.82  tff(c_9751, plain, ('#skF_1'('#skF_7', k1_xboole_0)='#skF_1'('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_9545, c_223])).
% 8.04/2.82  tff(c_5449, plain, (![B_3404]: (k1_xboole_0!=B_3404 | '#skF_4'('#skF_6')='#skF_1'('#skF_7', B_3404))), inference(demodulation, [status(thm), theory('equality')], [c_4634, c_4537])).
% 8.04/2.82  tff(c_5491, plain, (![B_3404]: (r2_hidden('#skF_1'('#skF_7', B_3404), '#skF_6') | k1_xboole_0='#skF_6' | k1_xboole_0!=B_3404)), inference(superposition, [status(thm), theory('equality')], [c_5449, c_42])).
% 8.04/2.82  tff(c_5521, plain, (![B_3404]: (r2_hidden('#skF_1'('#skF_7', B_3404), '#skF_6') | k1_xboole_0!=B_3404)), inference(negUnitSimplification, [status(thm)], [c_916, c_5491])).
% 8.04/2.82  tff(c_9855, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_9751, c_5521])).
% 8.04/2.82  tff(c_11008, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_9855, c_4])).
% 8.04/2.82  tff(c_11032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_223, c_11008])).
% 8.04/2.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.04/2.82  
% 8.04/2.82  Inference rules
% 8.04/2.82  ----------------------
% 8.04/2.82  #Ref     : 1
% 8.04/2.82  #Sup     : 1893
% 8.04/2.82  #Fact    : 2
% 8.04/2.82  #Define  : 0
% 8.04/2.82  #Split   : 10
% 8.04/2.82  #Chain   : 0
% 8.04/2.82  #Close   : 0
% 8.04/2.82  
% 8.04/2.82  Ordering : KBO
% 8.04/2.82  
% 8.04/2.82  Simplification rules
% 8.04/2.82  ----------------------
% 8.04/2.82  #Subsume      : 689
% 8.04/2.82  #Demod        : 607
% 8.04/2.82  #Tautology    : 421
% 8.04/2.82  #SimpNegUnit  : 244
% 8.04/2.82  #BackRed      : 50
% 8.04/2.82  
% 8.04/2.82  #Partial instantiations: 5656
% 8.04/2.82  #Strategies tried      : 1
% 8.04/2.82  
% 8.04/2.82  Timing (in seconds)
% 8.04/2.82  ----------------------
% 8.04/2.82  Preprocessing        : 0.35
% 8.04/2.82  Parsing              : 0.18
% 8.04/2.82  CNF conversion       : 0.03
% 8.04/2.82  Main loop            : 1.59
% 8.04/2.82  Inferencing          : 0.59
% 8.04/2.82  Reduction            : 0.45
% 8.04/2.82  Demodulation         : 0.29
% 8.04/2.82  BG Simplification    : 0.05
% 8.04/2.82  Subsumption          : 0.40
% 8.04/2.82  Abstraction          : 0.07
% 8.04/2.82  MUC search           : 0.00
% 8.04/2.82  Cooper               : 0.00
% 8.04/2.82  Total                : 1.99
% 8.04/2.82  Index Insertion      : 0.00
% 8.04/2.82  Index Deletion       : 0.00
% 8.04/2.82  Index Matching       : 0.00
% 8.04/2.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
