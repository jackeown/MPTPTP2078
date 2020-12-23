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
% DateTime   : Thu Dec  3 10:16:54 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 279 expanded)
%              Number of leaves         :   32 ( 103 expanded)
%              Depth                    :   10
%              Number of atoms          :  161 ( 933 expanded)
%              Number of equality atoms :   28 ( 214 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_51,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_317,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( r2_relset_1(A_72,B_73,C_74,C_74)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_337,plain,(
    ! [C_76] :
      ( r2_relset_1('#skF_3','#skF_4',C_76,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_56,c_317])).

tff(c_350,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_337])).

tff(c_46,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_260,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_partfun1(C_69,A_70)
      | ~ v1_funct_2(C_69,A_70,B_71)
      | ~ v1_funct_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | v1_xboole_0(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_267,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_260])).

tff(c_284,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_267])).

tff(c_303,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_284])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_306,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_303,c_2])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_306])).

tff(c_311,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_312,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_270,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_260])).

tff(c_287,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_270])).

tff(c_313,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_313])).

tff(c_315,plain,(
    v1_partfun1('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_48,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_373,plain,(
    ! [D_80,C_81,A_82,B_83] :
      ( D_80 = C_81
      | ~ r1_partfun1(C_81,D_80)
      | ~ v1_partfun1(D_80,A_82)
      | ~ v1_partfun1(C_81,A_82)
      | ~ m1_subset_1(D_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_1(D_80)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_375,plain,(
    ! [A_82,B_83] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_82)
      | ~ v1_partfun1('#skF_5',A_82)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_373])).

tff(c_378,plain,(
    ! [A_82,B_83] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_82)
      | ~ v1_partfun1('#skF_5',A_82)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_375])).

tff(c_533,plain,(
    ! [A_108,B_109] :
      ( ~ v1_partfun1('#skF_6',A_108)
      | ~ v1_partfun1('#skF_5',A_108)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_536,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_56,c_533])).

tff(c_546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_311,c_315,c_536])).

tff(c_547,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_44,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_554,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_44])).

tff(c_564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_554])).

tff(c_566,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_565,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_573,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_565])).

tff(c_30,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_567,plain,(
    ! [A_12] : m1_subset_1('#skF_3',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_30])).

tff(c_584,plain,(
    ! [A_12] : m1_subset_1('#skF_4',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_567])).

tff(c_764,plain,(
    ! [A_141,B_142,C_143,D_144] :
      ( r2_relset_1(A_141,B_142,C_143,C_143)
      | ~ m1_subset_1(D_144,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_774,plain,(
    ! [A_145,B_146,C_147] :
      ( r2_relset_1(A_145,B_146,C_147,C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(resolution,[status(thm)],[c_584,c_764])).

tff(c_782,plain,(
    ! [A_145,B_146] : r2_relset_1(A_145,B_146,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_584,c_774])).

tff(c_28,plain,(
    ! [A_11] : ~ v1_xboole_0(k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_621,plain,(
    ! [A_118,B_119] :
      ( r2_hidden(A_118,B_119)
      | v1_xboole_0(B_119)
      | ~ m1_subset_1(A_118,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [C_8,A_4] :
      ( r1_tarski(C_8,A_4)
      | ~ r2_hidden(C_8,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_625,plain,(
    ! [A_118,A_4] :
      ( r1_tarski(A_118,A_4)
      | v1_xboole_0(k1_zfmisc_1(A_4))
      | ~ m1_subset_1(A_118,k1_zfmisc_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_621,c_10])).

tff(c_629,plain,(
    ! [A_120,A_121] :
      ( r1_tarski(A_120,A_121)
      | ~ m1_subset_1(A_120,k1_zfmisc_1(A_121)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_625])).

tff(c_641,plain,(
    ! [A_12] : r1_tarski('#skF_4',A_12) ),
    inference(resolution,[status(thm)],[c_584,c_629])).

tff(c_24,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_588,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_566,c_24])).

tff(c_614,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_573,c_56])).

tff(c_639,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_614,c_629])).

tff(c_655,plain,(
    ! [B_125,A_126] :
      ( B_125 = A_126
      | ~ r1_tarski(B_125,A_126)
      | ~ r1_tarski(A_126,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_661,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_639,c_655])).

tff(c_670,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_661])).

tff(c_613,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_573,c_50])).

tff(c_640,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_613,c_629])).

tff(c_659,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_640,c_655])).

tff(c_667,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_659])).

tff(c_596,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_44])).

tff(c_677,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_667,c_596])).

tff(c_717,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_677])).

tff(c_785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_717])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:30:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.43  
% 2.90/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.43  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.90/1.43  
% 2.90/1.43  %Foreground sorts:
% 2.90/1.43  
% 2.90/1.43  
% 2.90/1.43  %Background operators:
% 2.90/1.43  
% 2.90/1.43  
% 2.90/1.43  %Foreground operators:
% 2.90/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.90/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.43  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.90/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.90/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.90/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.90/1.43  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.90/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.90/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.90/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.90/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.90/1.43  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.90/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.43  
% 2.90/1.45  tff(f_125, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 2.90/1.45  tff(f_71, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.90/1.45  tff(f_85, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.90/1.45  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.90/1.45  tff(f_102, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.90/1.45  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.90/1.45  tff(f_51, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.90/1.45  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.90/1.45  tff(f_42, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.90/1.45  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.90/1.45  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.90/1.45  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.45  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.45  tff(c_317, plain, (![A_72, B_73, C_74, D_75]: (r2_relset_1(A_72, B_73, C_74, C_74) | ~m1_subset_1(D_75, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.90/1.45  tff(c_337, plain, (![C_76]: (r2_relset_1('#skF_3', '#skF_4', C_76, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_56, c_317])).
% 2.90/1.45  tff(c_350, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_337])).
% 2.90/1.45  tff(c_46, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.45  tff(c_66, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_46])).
% 2.90/1.45  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.45  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.45  tff(c_260, plain, (![C_69, A_70, B_71]: (v1_partfun1(C_69, A_70) | ~v1_funct_2(C_69, A_70, B_71) | ~v1_funct_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | v1_xboole_0(B_71))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.90/1.45  tff(c_267, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_260])).
% 2.90/1.45  tff(c_284, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_267])).
% 2.90/1.45  tff(c_303, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_284])).
% 2.90/1.45  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.90/1.45  tff(c_306, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_303, c_2])).
% 2.90/1.45  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_306])).
% 2.90/1.45  tff(c_311, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_284])).
% 2.90/1.45  tff(c_312, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_284])).
% 2.90/1.45  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.45  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.45  tff(c_270, plain, (v1_partfun1('#skF_6', '#skF_3') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_260])).
% 2.90/1.45  tff(c_287, plain, (v1_partfun1('#skF_6', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_270])).
% 2.90/1.45  tff(c_313, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_287])).
% 2.90/1.45  tff(c_314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_312, c_313])).
% 2.90/1.45  tff(c_315, plain, (v1_partfun1('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_287])).
% 2.90/1.45  tff(c_48, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.45  tff(c_373, plain, (![D_80, C_81, A_82, B_83]: (D_80=C_81 | ~r1_partfun1(C_81, D_80) | ~v1_partfun1(D_80, A_82) | ~v1_partfun1(C_81, A_82) | ~m1_subset_1(D_80, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_1(D_80) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_1(C_81))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.90/1.45  tff(c_375, plain, (![A_82, B_83]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_82) | ~v1_partfun1('#skF_5', A_82) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_373])).
% 2.90/1.45  tff(c_378, plain, (![A_82, B_83]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_82) | ~v1_partfun1('#skF_5', A_82) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_375])).
% 2.90/1.45  tff(c_533, plain, (![A_108, B_109]: (~v1_partfun1('#skF_6', A_108) | ~v1_partfun1('#skF_5', A_108) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(splitLeft, [status(thm)], [c_378])).
% 2.90/1.45  tff(c_536, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_56, c_533])).
% 2.90/1.45  tff(c_546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_311, c_315, c_536])).
% 2.90/1.45  tff(c_547, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_378])).
% 2.90/1.45  tff(c_44, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.45  tff(c_554, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_547, c_44])).
% 2.90/1.45  tff(c_564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_350, c_554])).
% 2.90/1.45  tff(c_566, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 2.90/1.45  tff(c_565, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_46])).
% 2.90/1.45  tff(c_573, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_566, c_565])).
% 2.90/1.45  tff(c_30, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.90/1.45  tff(c_567, plain, (![A_12]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_565, c_30])).
% 2.90/1.45  tff(c_584, plain, (![A_12]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_573, c_567])).
% 2.90/1.45  tff(c_764, plain, (![A_141, B_142, C_143, D_144]: (r2_relset_1(A_141, B_142, C_143, C_143) | ~m1_subset_1(D_144, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.90/1.45  tff(c_774, plain, (![A_145, B_146, C_147]: (r2_relset_1(A_145, B_146, C_147, C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(resolution, [status(thm)], [c_584, c_764])).
% 2.90/1.45  tff(c_782, plain, (![A_145, B_146]: (r2_relset_1(A_145, B_146, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_584, c_774])).
% 2.90/1.45  tff(c_28, plain, (![A_11]: (~v1_xboole_0(k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.90/1.45  tff(c_621, plain, (![A_118, B_119]: (r2_hidden(A_118, B_119) | v1_xboole_0(B_119) | ~m1_subset_1(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.90/1.45  tff(c_10, plain, (![C_8, A_4]: (r1_tarski(C_8, A_4) | ~r2_hidden(C_8, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.90/1.45  tff(c_625, plain, (![A_118, A_4]: (r1_tarski(A_118, A_4) | v1_xboole_0(k1_zfmisc_1(A_4)) | ~m1_subset_1(A_118, k1_zfmisc_1(A_4)))), inference(resolution, [status(thm)], [c_621, c_10])).
% 2.90/1.45  tff(c_629, plain, (![A_120, A_121]: (r1_tarski(A_120, A_121) | ~m1_subset_1(A_120, k1_zfmisc_1(A_121)))), inference(negUnitSimplification, [status(thm)], [c_28, c_625])).
% 2.90/1.45  tff(c_641, plain, (![A_12]: (r1_tarski('#skF_4', A_12))), inference(resolution, [status(thm)], [c_584, c_629])).
% 2.90/1.45  tff(c_24, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.90/1.45  tff(c_588, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_566, c_566, c_24])).
% 2.90/1.45  tff(c_614, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_588, c_573, c_56])).
% 2.90/1.45  tff(c_639, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_614, c_629])).
% 2.90/1.45  tff(c_655, plain, (![B_125, A_126]: (B_125=A_126 | ~r1_tarski(B_125, A_126) | ~r1_tarski(A_126, B_125))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.90/1.45  tff(c_661, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_639, c_655])).
% 2.90/1.45  tff(c_670, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_641, c_661])).
% 2.90/1.45  tff(c_613, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_588, c_573, c_50])).
% 2.90/1.45  tff(c_640, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_613, c_629])).
% 2.90/1.45  tff(c_659, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_640, c_655])).
% 2.90/1.45  tff(c_667, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_641, c_659])).
% 2.90/1.45  tff(c_596, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_573, c_44])).
% 2.90/1.45  tff(c_677, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_667, c_596])).
% 2.90/1.45  tff(c_717, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_670, c_677])).
% 2.90/1.45  tff(c_785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_782, c_717])).
% 2.90/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.45  
% 2.90/1.45  Inference rules
% 2.90/1.45  ----------------------
% 2.90/1.45  #Ref     : 0
% 2.90/1.45  #Sup     : 147
% 2.90/1.45  #Fact    : 0
% 2.90/1.45  #Define  : 0
% 2.90/1.45  #Split   : 13
% 2.90/1.45  #Chain   : 0
% 2.90/1.45  #Close   : 0
% 2.90/1.45  
% 2.90/1.45  Ordering : KBO
% 2.90/1.45  
% 2.90/1.45  Simplification rules
% 2.90/1.45  ----------------------
% 2.90/1.45  #Subsume      : 15
% 2.90/1.45  #Demod        : 92
% 2.90/1.45  #Tautology    : 70
% 2.90/1.45  #SimpNegUnit  : 14
% 2.90/1.45  #BackRed      : 26
% 2.90/1.45  
% 2.90/1.45  #Partial instantiations: 0
% 2.90/1.45  #Strategies tried      : 1
% 2.90/1.45  
% 2.90/1.45  Timing (in seconds)
% 2.90/1.45  ----------------------
% 2.90/1.45  Preprocessing        : 0.32
% 2.90/1.45  Parsing              : 0.17
% 2.90/1.45  CNF conversion       : 0.02
% 2.90/1.45  Main loop            : 0.35
% 2.90/1.45  Inferencing          : 0.13
% 2.90/1.45  Reduction            : 0.11
% 2.90/1.45  Demodulation         : 0.07
% 2.90/1.45  BG Simplification    : 0.02
% 2.90/1.45  Subsumption          : 0.06
% 2.90/1.45  Abstraction          : 0.01
% 2.90/1.45  MUC search           : 0.00
% 2.90/1.45  Cooper               : 0.00
% 2.90/1.45  Total                : 0.71
% 2.90/1.46  Index Insertion      : 0.00
% 2.90/1.46  Index Deletion       : 0.00
% 2.90/1.46  Index Matching       : 0.00
% 2.90/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
