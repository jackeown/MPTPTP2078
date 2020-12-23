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
% DateTime   : Thu Dec  3 10:10:58 EST 2020

% Result     : Theorem 27.00s
% Output     : CNFRefutation 27.93s
% Verified   : 
% Statistics : Number of formulae       : 1374 (77170 expanded)
%              Number of leaves         :   41 (26046 expanded)
%              Depth                    :   35
%              Number of atoms          : 2577 (203576 expanded)
%              Number of equality atoms :  541 (34645 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_141,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( k1_relat_1(C) = A
            & ! [D] :
                ( r2_hidden(D,A)
               => r2_hidden(k1_funct_1(C,D),B) ) )
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_123,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_82,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_80,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_78,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_157505,plain,(
    ! [A_22798,C_22799] :
      ( r2_hidden('#skF_5'(A_22798,k2_relat_1(A_22798),C_22799),k1_relat_1(A_22798))
      | ~ r2_hidden(C_22799,k2_relat_1(A_22798))
      | ~ v1_funct_1(A_22798)
      | ~ v1_relat_1(A_22798) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_157516,plain,(
    ! [C_22799] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_22799),'#skF_6')
      | ~ r2_hidden(C_22799,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_157505])).

tff(c_157523,plain,(
    ! [C_22800] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_22800),'#skF_6')
      | ~ r2_hidden(C_22800,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_157516])).

tff(c_157291,plain,(
    ! [A_22784,C_22785] :
      ( k1_funct_1(A_22784,'#skF_5'(A_22784,k2_relat_1(A_22784),C_22785)) = C_22785
      | ~ r2_hidden(C_22785,k2_relat_1(A_22784))
      | ~ v1_funct_1(A_22784)
      | ~ v1_relat_1(A_22784) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_76,plain,(
    ! [D_77] :
      ( r2_hidden(k1_funct_1('#skF_8',D_77),'#skF_7')
      | ~ r2_hidden(D_77,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_157321,plain,(
    ! [C_22785] :
      ( r2_hidden(C_22785,'#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_22785),'#skF_6')
      | ~ r2_hidden(C_22785,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157291,c_76])).

tff(c_157340,plain,(
    ! [C_22785] :
      ( r2_hidden(C_22785,'#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_22785),'#skF_6')
      | ~ r2_hidden(C_22785,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_157321])).

tff(c_157535,plain,(
    ! [C_22801] :
      ( r2_hidden(C_22801,'#skF_7')
      | ~ r2_hidden(C_22801,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_157523,c_157340])).

tff(c_157558,plain,(
    ! [B_22802] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_8'),B_22802),'#skF_7')
      | r1_tarski(k2_relat_1('#skF_8'),B_22802) ) ),
    inference(resolution,[status(thm)],[c_6,c_157535])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_157569,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_157558,c_4])).

tff(c_156218,plain,(
    ! [A_22650] :
      ( r1_tarski(A_22650,k2_zfmisc_1(k1_relat_1(A_22650),k2_relat_1(A_22650)))
      | ~ v1_relat_1(A_22650) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_156223,plain,
    ( r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8')))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_156218])).

tff(c_156226,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_156223])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_157591,plain,(
    ! [D_22805,C_22806,B_22807,A_22808] :
      ( m1_subset_1(D_22805,k1_zfmisc_1(k2_zfmisc_1(C_22806,B_22807)))
      | ~ r1_tarski(k2_relat_1(D_22805),B_22807)
      | ~ m1_subset_1(D_22805,k1_zfmisc_1(k2_zfmisc_1(C_22806,A_22808))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_162193,plain,(
    ! [A_23015,C_23016,B_23017,A_23018] :
      ( m1_subset_1(A_23015,k1_zfmisc_1(k2_zfmisc_1(C_23016,B_23017)))
      | ~ r1_tarski(k2_relat_1(A_23015),B_23017)
      | ~ r1_tarski(A_23015,k2_zfmisc_1(C_23016,A_23018)) ) ),
    inference(resolution,[status(thm)],[c_22,c_157591])).

tff(c_162326,plain,(
    ! [B_23025] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_23025)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_23025) ) ),
    inference(resolution,[status(thm)],[c_156226,c_162193])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_264,plain,(
    ! [C_122,B_123,A_124] :
      ( v5_relat_1(C_122,B_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_282,plain,(
    ! [C_126,B_127] :
      ( v5_relat_1(C_126,B_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_264])).

tff(c_286,plain,(
    ! [A_10,B_127] :
      ( v5_relat_1(A_10,B_127)
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_282])).

tff(c_212,plain,(
    ! [B_116,A_117] :
      ( r1_tarski(k2_relat_1(B_116),A_117)
      | ~ v5_relat_1(B_116,A_117)
      | ~ v1_relat_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_143,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_1'(A_94,B_95),A_94)
      | r1_tarski(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [B_62,A_61] :
      ( ~ r1_tarski(B_62,A_61)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_153,plain,(
    ! [A_94,B_95] :
      ( ~ r1_tarski(A_94,'#skF_1'(A_94,B_95))
      | r1_tarski(A_94,B_95) ) ),
    inference(resolution,[status(thm)],[c_143,c_52])).

tff(c_117424,plain,(
    ! [B_20982,B_20983] :
      ( r1_tarski(k2_relat_1(B_20982),B_20983)
      | ~ v5_relat_1(B_20982,'#skF_1'(k2_relat_1(B_20982),B_20983))
      | ~ v1_relat_1(B_20982) ) ),
    inference(resolution,[status(thm)],[c_212,c_153])).

tff(c_117451,plain,(
    ! [A_10,B_20983] :
      ( r1_tarski(k2_relat_1(A_10),B_20983)
      | ~ v1_relat_1(A_10)
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_286,c_117424])).

tff(c_117387,plain,(
    ! [A_20977,D_20978] :
      ( r2_hidden(k1_funct_1(A_20977,D_20978),k2_relat_1(A_20977))
      | ~ r2_hidden(D_20978,k1_relat_1(A_20977))
      | ~ v1_funct_1(A_20977)
      | ~ v1_relat_1(A_20977) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_145015,plain,(
    ! [A_22111,D_22112] :
      ( ~ r1_tarski(k2_relat_1(A_22111),k1_funct_1(A_22111,D_22112))
      | ~ r2_hidden(D_22112,k1_relat_1(A_22111))
      | ~ v1_funct_1(A_22111)
      | ~ v1_relat_1(A_22111) ) ),
    inference(resolution,[status(thm)],[c_117387,c_52])).

tff(c_150784,plain,(
    ! [D_22320,A_22321] :
      ( ~ r2_hidden(D_22320,k1_relat_1(A_22321))
      | ~ v1_funct_1(A_22321)
      | ~ v1_relat_1(A_22321)
      | ~ r1_tarski(A_22321,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_117451,c_145015])).

tff(c_150852,plain,(
    ! [D_22320] :
      ( ~ r2_hidden(D_22320,'#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_150784])).

tff(c_150872,plain,(
    ! [D_22320] :
      ( ~ r2_hidden(D_22320,'#skF_6')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_150852])).

tff(c_150873,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_150872])).

tff(c_142084,plain,(
    ! [A_22004,D_22005] :
      ( ~ r1_tarski(k2_relat_1(A_22004),k1_funct_1(A_22004,D_22005))
      | ~ r2_hidden(D_22005,k1_relat_1(A_22004))
      | ~ v1_funct_1(A_22004)
      | ~ v1_relat_1(A_22004) ) ),
    inference(resolution,[status(thm)],[c_117387,c_52])).

tff(c_142146,plain,(
    ! [D_22006,A_22007] :
      ( ~ r2_hidden(D_22006,k1_relat_1(A_22007))
      | ~ v1_funct_1(A_22007)
      | ~ v1_relat_1(A_22007)
      | ~ r1_tarski(A_22007,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_117451,c_142084])).

tff(c_142210,plain,(
    ! [D_22006] :
      ( ~ r2_hidden(D_22006,'#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_142146])).

tff(c_142229,plain,(
    ! [D_22006] :
      ( ~ r2_hidden(D_22006,'#skF_6')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_142210])).

tff(c_142230,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_142229])).

tff(c_117544,plain,(
    ! [A_20988,C_20989] :
      ( r2_hidden('#skF_5'(A_20988,k2_relat_1(A_20988),C_20989),k1_relat_1(A_20988))
      | ~ r2_hidden(C_20989,k2_relat_1(A_20988))
      | ~ v1_funct_1(A_20988)
      | ~ v1_relat_1(A_20988) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_117555,plain,(
    ! [C_20989] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_20989),'#skF_6')
      | ~ r2_hidden(C_20989,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_117544])).

tff(c_117561,plain,(
    ! [C_20989] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_20989),'#skF_6')
      | ~ r2_hidden(C_20989,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_117555])).

tff(c_117881,plain,(
    ! [A_21000,C_21001] :
      ( k1_funct_1(A_21000,'#skF_5'(A_21000,k2_relat_1(A_21000),C_21001)) = C_21001
      | ~ r2_hidden(C_21001,k2_relat_1(A_21000))
      | ~ v1_funct_1(A_21000)
      | ~ v1_relat_1(A_21000) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_117915,plain,(
    ! [C_21001] :
      ( r2_hidden(C_21001,'#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_21001),'#skF_6')
      | ~ r2_hidden(C_21001,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117881,c_76])).

tff(c_117986,plain,(
    ! [C_21005] :
      ( r2_hidden(C_21005,'#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_21005),'#skF_6')
      | ~ r2_hidden(C_21005,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_117915])).

tff(c_117991,plain,(
    ! [C_21006] :
      ( r2_hidden(C_21006,'#skF_7')
      | ~ r2_hidden(C_21006,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_117561,c_117986])).

tff(c_118014,plain,(
    ! [B_21007] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_8'),B_21007),'#skF_7')
      | r1_tarski(k2_relat_1('#skF_8'),B_21007) ) ),
    inference(resolution,[status(thm)],[c_6,c_117991])).

tff(c_118025,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_118014,c_4])).

tff(c_24,plain,(
    ! [B_13,A_12] :
      ( v5_relat_1(B_13,A_12)
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_118031,plain,
    ( v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_118025,c_24])).

tff(c_118037,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_118031])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_84,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_74])).

tff(c_167,plain,(
    ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_32,plain,(
    ! [A_20] :
      ( r1_tarski(A_20,k2_zfmisc_1(k1_relat_1(A_20),k2_relat_1(A_20)))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_118045,plain,(
    ! [D_21008,C_21009,B_21010,A_21011] :
      ( m1_subset_1(D_21008,k1_zfmisc_1(k2_zfmisc_1(C_21009,B_21010)))
      | ~ r1_tarski(k2_relat_1(D_21008),B_21010)
      | ~ m1_subset_1(D_21008,k1_zfmisc_1(k2_zfmisc_1(C_21009,A_21011))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_142679,plain,(
    ! [A_22024,C_22025,B_22026,A_22027] :
      ( m1_subset_1(A_22024,k1_zfmisc_1(k2_zfmisc_1(C_22025,B_22026)))
      | ~ r1_tarski(k2_relat_1(A_22024),B_22026)
      | ~ r1_tarski(A_22024,k2_zfmisc_1(C_22025,A_22027)) ) ),
    inference(resolution,[status(thm)],[c_22,c_118045])).

tff(c_143537,plain,(
    ! [A_22067,B_22068] :
      ( m1_subset_1(A_22067,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_22067),B_22068)))
      | ~ r1_tarski(k2_relat_1(A_22067),B_22068)
      | ~ v1_relat_1(A_22067) ) ),
    inference(resolution,[status(thm)],[c_32,c_142679])).

tff(c_143567,plain,(
    ! [B_22068] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_22068)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_22068)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_143537])).

tff(c_143579,plain,(
    ! [B_22069] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_22069)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_22069) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_143567])).

tff(c_58,plain,(
    ! [A_66,B_67,C_68] :
      ( k1_relset_1(A_66,B_67,C_68) = k1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_143590,plain,(
    ! [B_22069] :
      ( k1_relset_1('#skF_6',B_22069,'#skF_8') = k1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_22069) ) ),
    inference(resolution,[status(thm)],[c_143579,c_58])).

tff(c_143718,plain,(
    ! [B_22071] :
      ( k1_relset_1('#skF_6',B_22071,'#skF_8') = '#skF_6'
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_22071) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_143590])).

tff(c_143761,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_118025,c_143718])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_143819,plain,(
    ! [B_22075] :
      ( r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',B_22075))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_22075) ) ),
    inference(resolution,[status(thm)],[c_143579,c_20])).

tff(c_143862,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_118025,c_143819])).

tff(c_118210,plain,(
    ! [B_21020,C_21021,A_21022] :
      ( k1_xboole_0 = B_21020
      | v1_funct_2(C_21021,A_21022,B_21020)
      | k1_relset_1(A_21022,B_21020,C_21021) != A_21022
      | ~ m1_subset_1(C_21021,k1_zfmisc_1(k2_zfmisc_1(A_21022,B_21020))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_118224,plain,(
    ! [B_21020,A_10,A_21022] :
      ( k1_xboole_0 = B_21020
      | v1_funct_2(A_10,A_21022,B_21020)
      | k1_relset_1(A_21022,B_21020,A_10) != A_21022
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_21022,B_21020)) ) ),
    inference(resolution,[status(thm)],[c_22,c_118210])).

tff(c_143874,plain,
    ( k1_xboole_0 = '#skF_7'
    | v1_funct_2('#skF_8','#skF_6','#skF_7')
    | k1_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_143862,c_118224])).

tff(c_143894,plain,
    ( k1_xboole_0 = '#skF_7'
    | v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143761,c_143874])).

tff(c_143895,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_143894])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_142428,plain,(
    ! [D_22012,A_22013,B_22014] :
      ( m1_subset_1(D_22012,k1_zfmisc_1(k2_zfmisc_1(A_22013,B_22014)))
      | ~ r1_tarski(k2_relat_1(D_22012),B_22014)
      | ~ m1_subset_1(D_22012,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_118045])).

tff(c_142953,plain,(
    ! [D_22035,A_22036,B_22037] :
      ( r1_tarski(D_22035,k2_zfmisc_1(A_22036,B_22037))
      | ~ r1_tarski(k2_relat_1(D_22035),B_22037)
      | ~ m1_subset_1(D_22035,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_142428,c_20])).

tff(c_142991,plain,(
    ! [A_22036] :
      ( r1_tarski('#skF_8',k2_zfmisc_1(A_22036,'#skF_7'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_118025,c_142953])).

tff(c_143231,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_142991])).

tff(c_143606,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_143579])).

tff(c_143618,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_143231,c_143606])).

tff(c_143648,plain,
    ( ~ v5_relat_1('#skF_8',k1_xboole_0)
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_143618])).

tff(c_143655,plain,(
    ~ v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_143648])).

tff(c_143906,plain,(
    ~ v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143895,c_143655])).

tff(c_144014,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118037,c_143906])).

tff(c_144016,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_142991])).

tff(c_144029,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_144016,c_20])).

tff(c_144040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142230,c_144029])).

tff(c_144041,plain,(
    ! [D_22006] : ~ r2_hidden(D_22006,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_142229])).

tff(c_117,plain,(
    ! [A_81,B_82] : v1_relat_1(k2_zfmisc_1(A_81,B_82)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_119,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_117])).

tff(c_105372,plain,(
    ! [A_15611,B_15612,A_15613] :
      ( v5_relat_1(A_15611,B_15612)
      | ~ r1_tarski(A_15611,k2_zfmisc_1(A_15613,B_15612)) ) ),
    inference(resolution,[status(thm)],[c_22,c_264])).

tff(c_105404,plain,(
    ! [A_15616,B_15617] : v5_relat_1(k2_zfmisc_1(A_15616,B_15617),B_15617) ),
    inference(resolution,[status(thm)],[c_12,c_105372])).

tff(c_105410,plain,(
    ! [B_9] : v5_relat_1(k1_xboole_0,B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_105404])).

tff(c_117440,plain,(
    ! [B_20983] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),B_20983)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_105410,c_117424])).

tff(c_117450,plain,(
    ! [B_20983] : r1_tarski(k2_relat_1(k1_xboole_0),B_20983) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_117440])).

tff(c_135903,plain,(
    ! [A_21758,B_21759] :
      ( r2_hidden('#skF_3'(A_21758,B_21759),k1_relat_1(A_21758))
      | r2_hidden('#skF_4'(A_21758,B_21759),B_21759)
      | k2_relat_1(A_21758) = B_21759
      | ~ v1_funct_1(A_21758)
      | ~ v1_relat_1(A_21758) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_135927,plain,(
    ! [B_21759] :
      ( r2_hidden('#skF_3'('#skF_8',B_21759),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_21759),B_21759)
      | k2_relat_1('#skF_8') = B_21759
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_135903])).

tff(c_135950,plain,(
    ! [B_21762] :
      ( r2_hidden('#skF_3'('#skF_8',B_21762),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_21762),B_21762)
      | k2_relat_1('#skF_8') = B_21762 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_135927])).

tff(c_136092,plain,(
    ! [B_21767] :
      ( ~ r1_tarski(B_21767,'#skF_4'('#skF_8',B_21767))
      | r2_hidden('#skF_3'('#skF_8',B_21767),'#skF_6')
      | k2_relat_1('#skF_8') = B_21767 ) ),
    inference(resolution,[status(thm)],[c_135950,c_52])).

tff(c_136108,plain,
    ( r2_hidden('#skF_3'('#skF_8',k2_relat_1(k1_xboole_0)),'#skF_6')
    | k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_117450,c_136092])).

tff(c_136164,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_136108])).

tff(c_136173,plain,(
    ! [B_20983] : r1_tarski(k2_relat_1('#skF_8'),B_20983) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136164,c_117450])).

tff(c_136927,plain,(
    ! [A_21798,D_21799] :
      ( ~ r1_tarski(k2_relat_1(A_21798),k1_funct_1(A_21798,D_21799))
      | ~ r2_hidden(D_21799,k1_relat_1(A_21798))
      | ~ v1_funct_1(A_21798)
      | ~ v1_relat_1(A_21798) ) ),
    inference(resolution,[status(thm)],[c_117387,c_52])).

tff(c_136934,plain,(
    ! [D_21799] :
      ( ~ r2_hidden(D_21799,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_136173,c_136927])).

tff(c_136965,plain,(
    ! [D_21800] : ~ r2_hidden(D_21800,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_136934])).

tff(c_137012,plain,(
    ! [B_21801] : r1_tarski('#skF_6',B_21801) ),
    inference(resolution,[status(thm)],[c_6,c_136965])).

tff(c_117452,plain,(
    ! [B_20984] : r1_tarski(k2_relat_1(k1_xboole_0),B_20984) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_117440])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_117510,plain,(
    ! [B_20984] :
      ( k2_relat_1(k1_xboole_0) = B_20984
      | ~ r1_tarski(B_20984,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_117452,c_8])).

tff(c_136171,plain,(
    ! [B_20984] :
      ( k2_relat_1('#skF_8') = B_20984
      | ~ r1_tarski(B_20984,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136164,c_136164,c_117510])).

tff(c_137059,plain,(
    k2_relat_1('#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_137012,c_136171])).

tff(c_91498,plain,(
    ! [B_12012,B_12013] :
      ( r1_tarski(k2_relat_1(B_12012),B_12013)
      | ~ v5_relat_1(B_12012,'#skF_1'(k2_relat_1(B_12012),B_12013))
      | ~ v1_relat_1(B_12012) ) ),
    inference(resolution,[status(thm)],[c_212,c_153])).

tff(c_91539,plain,(
    ! [A_10,B_12013] :
      ( r1_tarski(k2_relat_1(A_10),B_12013)
      | ~ v1_relat_1(A_10)
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_286,c_91498])).

tff(c_91448,plain,(
    ! [A_12001,D_12002] :
      ( r2_hidden(k1_funct_1(A_12001,D_12002),k2_relat_1(A_12001))
      | ~ r2_hidden(D_12002,k1_relat_1(A_12001))
      | ~ v1_funct_1(A_12001)
      | ~ v1_relat_1(A_12001) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_103736,plain,(
    ! [A_15548,D_15549] :
      ( ~ r1_tarski(k2_relat_1(A_15548),k1_funct_1(A_15548,D_15549))
      | ~ r2_hidden(D_15549,k1_relat_1(A_15548))
      | ~ v1_funct_1(A_15548)
      | ~ v1_relat_1(A_15548) ) ),
    inference(resolution,[status(thm)],[c_91448,c_52])).

tff(c_103763,plain,(
    ! [D_15550,A_15551] :
      ( ~ r2_hidden(D_15550,k1_relat_1(A_15551))
      | ~ v1_funct_1(A_15551)
      | ~ v1_relat_1(A_15551)
      | ~ r1_tarski(A_15551,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_91539,c_103736])).

tff(c_103819,plain,(
    ! [D_15550] :
      ( ~ r2_hidden(D_15550,'#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_103763])).

tff(c_103836,plain,(
    ! [D_15550] :
      ( ~ r2_hidden(D_15550,'#skF_6')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_103819])).

tff(c_103837,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_103836])).

tff(c_92122,plain,(
    ! [A_12037,C_12038] :
      ( r2_hidden('#skF_5'(A_12037,k2_relat_1(A_12037),C_12038),k1_relat_1(A_12037))
      | ~ r2_hidden(C_12038,k2_relat_1(A_12037))
      | ~ v1_funct_1(A_12037)
      | ~ v1_relat_1(A_12037) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_92136,plain,(
    ! [C_12038] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_12038),'#skF_6')
      | ~ r2_hidden(C_12038,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_92122])).

tff(c_92279,plain,(
    ! [C_12042] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_12042),'#skF_6')
      | ~ r2_hidden(C_12042,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_92136])).

tff(c_91599,plain,(
    ! [A_12015,C_12016] :
      ( k1_funct_1(A_12015,'#skF_5'(A_12015,k2_relat_1(A_12015),C_12016)) = C_12016
      | ~ r2_hidden(C_12016,k2_relat_1(A_12015))
      | ~ v1_funct_1(A_12015)
      | ~ v1_relat_1(A_12015) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_91629,plain,(
    ! [C_12016] :
      ( r2_hidden(C_12016,'#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_12016),'#skF_6')
      | ~ r2_hidden(C_12016,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91599,c_76])).

tff(c_91645,plain,(
    ! [C_12016] :
      ( r2_hidden(C_12016,'#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_12016),'#skF_6')
      | ~ r2_hidden(C_12016,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_91629])).

tff(c_92291,plain,(
    ! [C_12043] :
      ( r2_hidden(C_12043,'#skF_7')
      | ~ r2_hidden(C_12043,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_92279,c_91645])).

tff(c_92314,plain,(
    ! [B_12044] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_8'),B_12044),'#skF_7')
      | r1_tarski(k2_relat_1('#skF_8'),B_12044) ) ),
    inference(resolution,[status(thm)],[c_6,c_92291])).

tff(c_92325,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_92314,c_4])).

tff(c_239,plain,(
    ! [A_121] :
      ( r1_tarski(A_121,k2_zfmisc_1(k1_relat_1(A_121),k2_relat_1(A_121)))
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_251,plain,
    ( r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8')))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_239])).

tff(c_256,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_251])).

tff(c_91925,plain,(
    ! [D_12026,C_12027,B_12028,A_12029] :
      ( m1_subset_1(D_12026,k1_zfmisc_1(k2_zfmisc_1(C_12027,B_12028)))
      | ~ r1_tarski(k2_relat_1(D_12026),B_12028)
      | ~ m1_subset_1(D_12026,k1_zfmisc_1(k2_zfmisc_1(C_12027,A_12029))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_104533,plain,(
    ! [A_15573,C_15574,B_15575,A_15576] :
      ( m1_subset_1(A_15573,k1_zfmisc_1(k2_zfmisc_1(C_15574,B_15575)))
      | ~ r1_tarski(k2_relat_1(A_15573),B_15575)
      | ~ r1_tarski(A_15573,k2_zfmisc_1(C_15574,A_15576)) ) ),
    inference(resolution,[status(thm)],[c_22,c_91925])).

tff(c_104662,plain,(
    ! [B_15583] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_15583)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_15583) ) ),
    inference(resolution,[status(thm)],[c_256,c_104533])).

tff(c_104673,plain,(
    ! [B_15583] :
      ( k1_relset_1('#skF_6',B_15583,'#skF_8') = k1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_15583) ) ),
    inference(resolution,[status(thm)],[c_104662,c_58])).

tff(c_104769,plain,(
    ! [B_15586] :
      ( k1_relset_1('#skF_6',B_15586,'#skF_8') = '#skF_6'
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_15586) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_104673])).

tff(c_104796,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_92325,c_104769])).

tff(c_104851,plain,(
    ! [B_15589] :
      ( r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',B_15589))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_15589) ) ),
    inference(resolution,[status(thm)],[c_104662,c_20])).

tff(c_104878,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_92325,c_104851])).

tff(c_102648,plain,(
    ! [B_15477,C_15478,A_15479] :
      ( k1_xboole_0 = B_15477
      | v1_funct_2(C_15478,A_15479,B_15477)
      | k1_relset_1(A_15479,B_15477,C_15478) != A_15479
      | ~ m1_subset_1(C_15478,k1_zfmisc_1(k2_zfmisc_1(A_15479,B_15477))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_105132,plain,(
    ! [B_15601,A_15602,A_15603] :
      ( k1_xboole_0 = B_15601
      | v1_funct_2(A_15602,A_15603,B_15601)
      | k1_relset_1(A_15603,B_15601,A_15602) != A_15603
      | ~ r1_tarski(A_15602,k2_zfmisc_1(A_15603,B_15601)) ) ),
    inference(resolution,[status(thm)],[c_22,c_102648])).

tff(c_105138,plain,
    ( k1_xboole_0 = '#skF_7'
    | v1_funct_2('#skF_8','#skF_6','#skF_7')
    | k1_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_104878,c_105132])).

tff(c_105182,plain,
    ( k1_xboole_0 = '#skF_7'
    | v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104796,c_105138])).

tff(c_105183,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_105182])).

tff(c_104686,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_104662])).

tff(c_104734,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_104686])).

tff(c_105204,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105183,c_104734])).

tff(c_105294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92325,c_105204])).

tff(c_105295,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_104686])).

tff(c_105309,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_105295,c_20])).

tff(c_105320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103837,c_105309])).

tff(c_105321,plain,(
    ! [D_15550] : ~ r2_hidden(D_15550,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_103836])).

tff(c_289,plain,(
    ! [A_130,B_131,A_132] :
      ( v5_relat_1(A_130,B_131)
      | ~ r1_tarski(A_130,k2_zfmisc_1(A_132,B_131)) ) ),
    inference(resolution,[status(thm)],[c_22,c_264])).

tff(c_321,plain,(
    ! [A_136,B_137] : v5_relat_1(k2_zfmisc_1(A_136,B_137),B_137) ),
    inference(resolution,[status(thm)],[c_12,c_289])).

tff(c_324,plain,(
    ! [B_9] : v5_relat_1(k1_xboole_0,B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_321])).

tff(c_91522,plain,(
    ! [B_12013] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),B_12013)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_324,c_91498])).

tff(c_91538,plain,(
    ! [B_12013] : r1_tarski(k2_relat_1(k1_xboole_0),B_12013) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_91522])).

tff(c_100431,plain,(
    ! [A_15388,D_15389] :
      ( ~ r1_tarski(k2_relat_1(A_15388),k1_funct_1(A_15388,D_15389))
      | ~ r2_hidden(D_15389,k1_relat_1(A_15388))
      | ~ v1_funct_1(A_15388)
      | ~ v1_relat_1(A_15388) ) ),
    inference(resolution,[status(thm)],[c_91448,c_52])).

tff(c_100608,plain,(
    ! [D_15398,A_15399] :
      ( ~ r2_hidden(D_15398,k1_relat_1(A_15399))
      | ~ v1_funct_1(A_15399)
      | ~ v1_relat_1(A_15399)
      | ~ r1_tarski(A_15399,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_91539,c_100431])).

tff(c_100668,plain,(
    ! [D_15398] :
      ( ~ r2_hidden(D_15398,'#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_100608])).

tff(c_100686,plain,(
    ! [D_15398] :
      ( ~ r2_hidden(D_15398,'#skF_6')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_100668])).

tff(c_100687,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_100686])).

tff(c_92331,plain,
    ( v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_92325,c_24])).

tff(c_92337,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_92331])).

tff(c_101273,plain,(
    ! [A_15425,C_15426,B_15427,A_15428] :
      ( m1_subset_1(A_15425,k1_zfmisc_1(k2_zfmisc_1(C_15426,B_15427)))
      | ~ r1_tarski(k2_relat_1(A_15425),B_15427)
      | ~ r1_tarski(A_15425,k2_zfmisc_1(C_15426,A_15428)) ) ),
    inference(resolution,[status(thm)],[c_22,c_91925])).

tff(c_101427,plain,(
    ! [B_15433] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_15433)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_15433) ) ),
    inference(resolution,[status(thm)],[c_256,c_101273])).

tff(c_101438,plain,(
    ! [B_15433] :
      ( k1_relset_1('#skF_6',B_15433,'#skF_8') = k1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_15433) ) ),
    inference(resolution,[status(thm)],[c_101427,c_58])).

tff(c_101581,plain,(
    ! [B_15440] :
      ( k1_relset_1('#skF_6',B_15440,'#skF_8') = '#skF_6'
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_15440) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_101438])).

tff(c_101605,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_92325,c_101581])).

tff(c_101665,plain,(
    ! [B_15443] :
      ( r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',B_15443))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_15443) ) ),
    inference(resolution,[status(thm)],[c_101427,c_20])).

tff(c_101689,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_92325,c_101665])).

tff(c_92551,plain,(
    ! [B_12061,C_12062,A_12063] :
      ( k1_xboole_0 = B_12061
      | v1_funct_2(C_12062,A_12063,B_12061)
      | k1_relset_1(A_12063,B_12061,C_12062) != A_12063
      | ~ m1_subset_1(C_12062,k1_zfmisc_1(k2_zfmisc_1(A_12063,B_12061))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_102131,plain,(
    ! [B_15462,A_15463,A_15464] :
      ( k1_xboole_0 = B_15462
      | v1_funct_2(A_15463,A_15464,B_15462)
      | k1_relset_1(A_15464,B_15462,A_15463) != A_15464
      | ~ r1_tarski(A_15463,k2_zfmisc_1(A_15464,B_15462)) ) ),
    inference(resolution,[status(thm)],[c_22,c_92551])).

tff(c_102143,plain,
    ( k1_xboole_0 = '#skF_7'
    | v1_funct_2('#skF_8','#skF_6','#skF_7')
    | k1_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_101689,c_102131])).

tff(c_102192,plain,
    ( k1_xboole_0 = '#skF_7'
    | v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101605,c_102143])).

tff(c_102193,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_102192])).

tff(c_101451,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_101427])).

tff(c_101497,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_101451])).

tff(c_101506,plain,
    ( ~ v5_relat_1('#skF_8',k1_xboole_0)
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_101497])).

tff(c_101513,plain,(
    ~ v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_101506])).

tff(c_102221,plain,(
    ~ v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102193,c_101513])).

tff(c_102305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92337,c_102221])).

tff(c_102306,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_101451])).

tff(c_102320,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_102306,c_20])).

tff(c_102331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100687,c_102320])).

tff(c_102332,plain,(
    ! [D_15398] : ~ r2_hidden(D_15398,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_100686])).

tff(c_92652,plain,(
    ! [A_12073,B_12074] :
      ( r2_hidden('#skF_3'(A_12073,B_12074),k1_relat_1(A_12073))
      | r2_hidden('#skF_4'(A_12073,B_12074),B_12074)
      | k2_relat_1(A_12073) = B_12074
      | ~ v1_funct_1(A_12073)
      | ~ v1_relat_1(A_12073) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_92676,plain,(
    ! [B_12074] :
      ( r2_hidden('#skF_3'('#skF_8',B_12074),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_12074),B_12074)
      | k2_relat_1('#skF_8') = B_12074
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_92652])).

tff(c_92689,plain,(
    ! [B_12075] :
      ( r2_hidden('#skF_3'('#skF_8',B_12075),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_12075),B_12075)
      | k2_relat_1('#skF_8') = B_12075 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_92676])).

tff(c_92758,plain,(
    ! [B_12077] :
      ( ~ r1_tarski(B_12077,'#skF_4'('#skF_8',B_12077))
      | r2_hidden('#skF_3'('#skF_8',B_12077),'#skF_6')
      | k2_relat_1('#skF_8') = B_12077 ) ),
    inference(resolution,[status(thm)],[c_92689,c_52])).

tff(c_92769,plain,
    ( r2_hidden('#skF_3'('#skF_8',k2_relat_1(k1_xboole_0)),'#skF_6')
    | k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_91538,c_92758])).

tff(c_92820,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_92769])).

tff(c_92831,plain,(
    ! [B_12013] : r1_tarski(k2_relat_1('#skF_8'),B_12013) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92820,c_91538])).

tff(c_93702,plain,(
    ! [A_12115,D_12116] :
      ( ~ r1_tarski(k2_relat_1(A_12115),k1_funct_1(A_12115,D_12116))
      | ~ r2_hidden(D_12116,k1_relat_1(A_12115))
      | ~ v1_funct_1(A_12115)
      | ~ v1_relat_1(A_12115) ) ),
    inference(resolution,[status(thm)],[c_91448,c_52])).

tff(c_93712,plain,(
    ! [D_12116] :
      ( ~ r2_hidden(D_12116,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_92831,c_93702])).

tff(c_93745,plain,(
    ! [D_12117] : ~ r2_hidden(D_12117,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_93712])).

tff(c_93783,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_93745])).

tff(c_93792,plain,(
    ! [B_12118] : r1_tarski('#skF_6',B_12118) ),
    inference(resolution,[status(thm)],[c_6,c_93745])).

tff(c_91540,plain,(
    ! [B_12014] : r1_tarski(k2_relat_1(k1_xboole_0),B_12014) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_91522])).

tff(c_91598,plain,(
    ! [B_12014] :
      ( k2_relat_1(k1_xboole_0) = B_12014
      | ~ r1_tarski(B_12014,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_91540,c_8])).

tff(c_92830,plain,(
    ! [B_12014] :
      ( k2_relat_1('#skF_8') = B_12014
      | ~ r1_tarski(B_12014,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92820,c_92820,c_91598])).

tff(c_93841,plain,(
    k2_relat_1('#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_93792,c_92830])).

tff(c_93872,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93841,c_256])).

tff(c_94280,plain,(
    ! [A_12122,C_12123,B_12124,A_12125] :
      ( m1_subset_1(A_12122,k1_zfmisc_1(k2_zfmisc_1(C_12123,B_12124)))
      | ~ r1_tarski(k2_relat_1(A_12122),B_12124)
      | ~ r1_tarski(A_12122,k2_zfmisc_1(C_12123,A_12125)) ) ),
    inference(resolution,[status(thm)],[c_22,c_91925])).

tff(c_94282,plain,(
    ! [B_12124] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_12124)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_12124) ) ),
    inference(resolution,[status(thm)],[c_93872,c_94280])).

tff(c_94753,plain,(
    ! [B_12146] : m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_12146))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93783,c_93841,c_94282])).

tff(c_94764,plain,(
    ! [B_12146] : k1_relset_1('#skF_6',B_12146,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_94753,c_58])).

tff(c_94783,plain,(
    ! [B_12146] : k1_relset_1('#skF_6',B_12146,'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_94764])).

tff(c_68,plain,(
    ! [B_74,C_75,A_73] :
      ( k1_xboole_0 = B_74
      | v1_funct_2(C_75,A_73,B_74)
      | k1_relset_1(A_73,B_74,C_75) != A_73
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_94777,plain,(
    ! [B_12146] :
      ( k1_xboole_0 = B_12146
      | v1_funct_2('#skF_8','#skF_6',B_12146)
      | k1_relset_1('#skF_6',B_12146,'#skF_8') != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_94753,c_68])).

tff(c_97446,plain,(
    ! [B_12258] :
      ( k1_xboole_0 = B_12258
      | v1_funct_2('#skF_8','#skF_6',B_12258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94783,c_94777])).

tff(c_97458,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_97446,c_167])).

tff(c_94776,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_94753])).

tff(c_375,plain,(
    ! [A_145,B_146,C_147] :
      ( k1_relset_1(A_145,B_146,C_147) = k1_relat_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_382,plain,(
    ! [B_9,C_147] :
      ( k1_relset_1(k1_xboole_0,B_9,C_147) = k1_relat_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_375])).

tff(c_94794,plain,(
    ! [B_9] : k1_relset_1(k1_xboole_0,B_9,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_94776,c_382])).

tff(c_94806,plain,(
    ! [B_9] : k1_relset_1(k1_xboole_0,B_9,'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_94794])).

tff(c_66,plain,(
    ! [C_75,B_74] :
      ( v1_funct_2(C_75,k1_xboole_0,B_74)
      | k1_relset_1(k1_xboole_0,B_74,C_75) != k1_xboole_0
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_85,plain,(
    ! [C_75,B_74] :
      ( v1_funct_2(C_75,k1_xboole_0,B_74)
      | k1_relset_1(k1_xboole_0,B_74,C_75) != k1_xboole_0
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_66])).

tff(c_94802,plain,(
    ! [B_74] :
      ( v1_funct_2('#skF_8',k1_xboole_0,B_74)
      | k1_relset_1(k1_xboole_0,B_74,'#skF_8') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_94776,c_85])).

tff(c_95514,plain,(
    ! [B_74] :
      ( v1_funct_2('#skF_8',k1_xboole_0,B_74)
      | k1_xboole_0 != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94806,c_94802])).

tff(c_95515,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_95514])).

tff(c_97471,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97458,c_95515])).

tff(c_97818,plain,(
    ! [A_12267] : k2_zfmisc_1(A_12267,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97458,c_97458,c_16])).

tff(c_28,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_313,plain,(
    ! [A_132,B_131] : v5_relat_1(k2_zfmisc_1(A_132,B_131),B_131) ),
    inference(resolution,[status(thm)],[c_12,c_289])).

tff(c_229,plain,(
    ! [B_116,A_117] :
      ( k2_relat_1(B_116) = A_117
      | ~ r1_tarski(A_117,k2_relat_1(B_116))
      | ~ v5_relat_1(B_116,A_117)
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_212,c_8])).

tff(c_92071,plain,(
    ! [B_12036] :
      ( k2_relat_1(k1_xboole_0) = k2_relat_1(B_12036)
      | ~ v5_relat_1(B_12036,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(B_12036) ) ),
    inference(resolution,[status(thm)],[c_91540,c_229])).

tff(c_92095,plain,(
    ! [A_132] :
      ( k2_relat_1(k2_zfmisc_1(A_132,k2_relat_1(k1_xboole_0))) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k2_zfmisc_1(A_132,k2_relat_1(k1_xboole_0))) ) ),
    inference(resolution,[status(thm)],[c_313,c_92071])).

tff(c_92116,plain,(
    ! [A_132] : k2_relat_1(k2_zfmisc_1(A_132,k2_relat_1(k1_xboole_0))) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_92095])).

tff(c_92823,plain,(
    ! [A_132] : k2_relat_1(k2_zfmisc_1(A_132,k2_relat_1('#skF_8'))) = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92820,c_92820,c_92116])).

tff(c_93856,plain,(
    ! [A_132] : k2_relat_1(k2_zfmisc_1(A_132,'#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93841,c_93841,c_92823])).

tff(c_94317,plain,(
    ! [A_12126] : k2_relat_1(k2_zfmisc_1(A_12126,'#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93841,c_93841,c_92823])).

tff(c_94374,plain,(
    ! [A_12126] :
      ( r1_tarski(k2_zfmisc_1(A_12126,'#skF_6'),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_12126,'#skF_6')),'#skF_6'))
      | ~ v1_relat_1(k2_zfmisc_1(A_12126,'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94317,c_32])).

tff(c_95717,plain,(
    ! [A_12201] : r1_tarski(k2_zfmisc_1(A_12201,'#skF_6'),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_12201,'#skF_6')),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_94374])).

tff(c_91933,plain,(
    ! [A_10,C_12027,B_12028,A_12029] :
      ( m1_subset_1(A_10,k1_zfmisc_1(k2_zfmisc_1(C_12027,B_12028)))
      | ~ r1_tarski(k2_relat_1(A_10),B_12028)
      | ~ r1_tarski(A_10,k2_zfmisc_1(C_12027,A_12029)) ) ),
    inference(resolution,[status(thm)],[c_22,c_91925])).

tff(c_95725,plain,(
    ! [A_12201,B_12028] :
      ( m1_subset_1(k2_zfmisc_1(A_12201,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_12201,'#skF_6')),B_12028)))
      | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(A_12201,'#skF_6')),B_12028) ) ),
    inference(resolution,[status(thm)],[c_95717,c_91933])).

tff(c_96968,plain,(
    ! [A_12239,B_12240] : m1_subset_1(k2_zfmisc_1(A_12239,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_12239,'#skF_6')),B_12240))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93783,c_93856,c_95725])).

tff(c_97010,plain,(
    ! [A_12239,B_12240] : r1_tarski(k2_zfmisc_1(A_12239,'#skF_6'),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_12239,'#skF_6')),B_12240)) ),
    inference(resolution,[status(thm)],[c_96968,c_20])).

tff(c_97823,plain,(
    ! [A_12239] : r1_tarski(k2_zfmisc_1(A_12239,'#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_97818,c_97010])).

tff(c_62,plain,(
    ! [A_73] :
      ( v1_funct_2(k1_xboole_0,A_73,k1_xboole_0)
      | k1_xboole_0 = A_73
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_73,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_88,plain,(
    ! [A_73] :
      ( v1_funct_2(k1_xboole_0,A_73,k1_xboole_0)
      | k1_xboole_0 = A_73
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_62])).

tff(c_338,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_341,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_338])).

tff(c_345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_341])).

tff(c_347,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_97510,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97458,c_97458,c_347])).

tff(c_93866,plain,(
    k2_relat_1(k1_xboole_0) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93841,c_92820])).

tff(c_97484,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97458,c_93866])).

tff(c_93612,plain,(
    ! [D_12108,A_12109,B_12110] :
      ( m1_subset_1(D_12108,k1_zfmisc_1(k2_zfmisc_1(A_12109,B_12110)))
      | ~ r1_tarski(k2_relat_1(D_12108),B_12110)
      | ~ m1_subset_1(D_12108,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_91925])).

tff(c_93645,plain,(
    ! [D_12108,A_12109,B_12110] :
      ( r1_tarski(D_12108,k2_zfmisc_1(A_12109,B_12110))
      | ~ r1_tarski(k2_relat_1(D_12108),B_12110)
      | ~ m1_subset_1(D_12108,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_93612,c_20])).

tff(c_98401,plain,(
    ! [D_12308,A_12309,B_12310] :
      ( r1_tarski(D_12308,k2_zfmisc_1(A_12309,B_12310))
      | ~ r1_tarski(k2_relat_1(D_12308),B_12310)
      | ~ m1_subset_1(D_12308,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97458,c_93645])).

tff(c_98403,plain,(
    ! [A_12309,B_12310] :
      ( r1_tarski('#skF_7',k2_zfmisc_1(A_12309,B_12310))
      | ~ r1_tarski('#skF_6',B_12310)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97484,c_98401])).

tff(c_98432,plain,(
    ! [A_12311,B_12312] : r1_tarski('#skF_7',k2_zfmisc_1(A_12311,B_12312)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97510,c_93783,c_98403])).

tff(c_99126,plain,(
    ! [A_12350,B_12351] :
      ( k2_zfmisc_1(A_12350,B_12351) = '#skF_7'
      | ~ r1_tarski(k2_zfmisc_1(A_12350,B_12351),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_98432,c_8])).

tff(c_99169,plain,(
    ! [A_12352] : k2_zfmisc_1(A_12352,'#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_97823,c_99126])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_97517,plain,(
    ! [B_9,A_8] :
      ( B_9 = '#skF_7'
      | A_8 = '#skF_7'
      | k2_zfmisc_1(A_8,B_9) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97458,c_97458,c_97458,c_14])).

tff(c_99188,plain,(
    ! [A_12352] :
      ( '#skF_7' = '#skF_6'
      | A_12352 = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99169,c_97517])).

tff(c_99282,plain,(
    ! [A_12353] : A_12353 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_97471,c_99188])).

tff(c_97481,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97458,c_94776])).

tff(c_98411,plain,(
    ! [A_12309,B_12310] :
      ( r1_tarski('#skF_8',k2_zfmisc_1(A_12309,B_12310))
      | ~ r1_tarski('#skF_6',B_12310)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93841,c_98401])).

tff(c_98463,plain,(
    ! [A_12313,B_12314] : r1_tarski('#skF_8',k2_zfmisc_1(A_12313,B_12314)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97481,c_93783,c_98411])).

tff(c_386,plain,(
    ! [A_145,B_146,A_10] :
      ( k1_relset_1(A_145,B_146,A_10) = k1_relat_1(A_10)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_145,B_146)) ) ),
    inference(resolution,[status(thm)],[c_22,c_375])).

tff(c_98468,plain,(
    ! [A_12313,B_12314] : k1_relset_1(A_12313,B_12314,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_98463,c_386])).

tff(c_98485,plain,(
    ! [A_12313,B_12314] : k1_relset_1(A_12313,B_12314,'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_98468])).

tff(c_99322,plain,(
    '#skF_7' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_99282,c_98485])).

tff(c_99731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97471,c_99322])).

tff(c_99733,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_95514])).

tff(c_94810,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_94776,c_20])).

tff(c_94825,plain,
    ( k1_xboole_0 = '#skF_8'
    | ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(resolution,[status(thm)],[c_94810,c_8])).

tff(c_94937,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_94825])).

tff(c_99738,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99733,c_94937])).

tff(c_99785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93783,c_99738])).

tff(c_99786,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_94825])).

tff(c_68914,plain,(
    ! [B_10985,B_10986] :
      ( r1_tarski(k2_relat_1(B_10985),B_10986)
      | ~ v5_relat_1(B_10985,'#skF_1'(k2_relat_1(B_10985),B_10986))
      | ~ v1_relat_1(B_10985) ) ),
    inference(resolution,[status(thm)],[c_212,c_153])).

tff(c_68938,plain,(
    ! [B_10986] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),B_10986)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_324,c_68914])).

tff(c_68954,plain,(
    ! [B_10986] : r1_tarski(k2_relat_1(k1_xboole_0),B_10986) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_68938])).

tff(c_68955,plain,(
    ! [A_10,B_10986] :
      ( r1_tarski(k2_relat_1(A_10),B_10986)
      | ~ v1_relat_1(A_10)
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_286,c_68914])).

tff(c_68903,plain,(
    ! [A_10983,D_10984] :
      ( r2_hidden(k1_funct_1(A_10983,D_10984),k2_relat_1(A_10983))
      | ~ r2_hidden(D_10984,k1_relat_1(A_10983))
      | ~ v1_funct_1(A_10983)
      | ~ v1_relat_1(A_10983) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_79136,plain,(
    ! [A_11417,D_11418] :
      ( ~ r1_tarski(k2_relat_1(A_11417),k1_funct_1(A_11417,D_11418))
      | ~ r2_hidden(D_11418,k1_relat_1(A_11417))
      | ~ v1_funct_1(A_11417)
      | ~ v1_relat_1(A_11417) ) ),
    inference(resolution,[status(thm)],[c_68903,c_52])).

tff(c_79183,plain,(
    ! [D_11419,A_11420] :
      ( ~ r2_hidden(D_11419,k1_relat_1(A_11420))
      | ~ v1_funct_1(A_11420)
      | ~ v1_relat_1(A_11420)
      | ~ r1_tarski(A_11420,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_68955,c_79136])).

tff(c_79244,plain,(
    ! [D_11419] :
      ( ~ r2_hidden(D_11419,'#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_79183])).

tff(c_79261,plain,(
    ! [D_11419] :
      ( ~ r2_hidden(D_11419,'#skF_6')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_79244])).

tff(c_79262,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_79261])).

tff(c_69466,plain,(
    ! [A_11005,C_11006] :
      ( r2_hidden('#skF_5'(A_11005,k2_relat_1(A_11005),C_11006),k1_relat_1(A_11005))
      | ~ r2_hidden(C_11006,k2_relat_1(A_11005))
      | ~ v1_funct_1(A_11005)
      | ~ v1_relat_1(A_11005) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_69477,plain,(
    ! [C_11006] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_11006),'#skF_6')
      | ~ r2_hidden(C_11006,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_69466])).

tff(c_69487,plain,(
    ! [C_11007] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_11007),'#skF_6')
      | ~ r2_hidden(C_11007,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_69477])).

tff(c_69261,plain,(
    ! [A_10993,C_10994] :
      ( k1_funct_1(A_10993,'#skF_5'(A_10993,k2_relat_1(A_10993),C_10994)) = C_10994
      | ~ r2_hidden(C_10994,k2_relat_1(A_10993))
      | ~ v1_funct_1(A_10993)
      | ~ v1_relat_1(A_10993) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_69291,plain,(
    ! [C_10994] :
      ( r2_hidden(C_10994,'#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_10994),'#skF_6')
      | ~ r2_hidden(C_10994,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69261,c_76])).

tff(c_69310,plain,(
    ! [C_10994] :
      ( r2_hidden(C_10994,'#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_10994),'#skF_6')
      | ~ r2_hidden(C_10994,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_69291])).

tff(c_69499,plain,(
    ! [C_11008] :
      ( r2_hidden(C_11008,'#skF_7')
      | ~ r2_hidden(C_11008,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_69487,c_69310])).

tff(c_69522,plain,(
    ! [B_11009] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_8'),B_11009),'#skF_7')
      | r1_tarski(k2_relat_1('#skF_8'),B_11009) ) ),
    inference(resolution,[status(thm)],[c_6,c_69499])).

tff(c_69533,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_69522,c_4])).

tff(c_69539,plain,
    ( v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_69533,c_24])).

tff(c_69545,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_69539])).

tff(c_69553,plain,(
    ! [D_11010,C_11011,B_11012,A_11013] :
      ( m1_subset_1(D_11010,k1_zfmisc_1(k2_zfmisc_1(C_11011,B_11012)))
      | ~ r1_tarski(k2_relat_1(D_11010),B_11012)
      | ~ m1_subset_1(D_11010,k1_zfmisc_1(k2_zfmisc_1(C_11011,A_11013))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_79813,plain,(
    ! [A_11446,C_11447,B_11448,A_11449] :
      ( m1_subset_1(A_11446,k1_zfmisc_1(k2_zfmisc_1(C_11447,B_11448)))
      | ~ r1_tarski(k2_relat_1(A_11446),B_11448)
      | ~ r1_tarski(A_11446,k2_zfmisc_1(C_11447,A_11449)) ) ),
    inference(resolution,[status(thm)],[c_22,c_69553])).

tff(c_79967,plain,(
    ! [B_11454] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_11454)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_11454) ) ),
    inference(resolution,[status(thm)],[c_256,c_79813])).

tff(c_79978,plain,(
    ! [B_11454] :
      ( k1_relset_1('#skF_6',B_11454,'#skF_8') = k1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_11454) ) ),
    inference(resolution,[status(thm)],[c_79967,c_58])).

tff(c_80078,plain,(
    ! [B_11457] :
      ( k1_relset_1('#skF_6',B_11457,'#skF_8') = '#skF_6'
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_11457) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_79978])).

tff(c_80102,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_69533,c_80078])).

tff(c_80162,plain,(
    ! [B_11460] :
      ( r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',B_11460))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_11460) ) ),
    inference(resolution,[status(thm)],[c_79967,c_20])).

tff(c_80186,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_69533,c_80162])).

tff(c_69845,plain,(
    ! [B_11027,C_11028,A_11029] :
      ( k1_xboole_0 = B_11027
      | v1_funct_2(C_11028,A_11029,B_11027)
      | k1_relset_1(A_11029,B_11027,C_11028) != A_11029
      | ~ m1_subset_1(C_11028,k1_zfmisc_1(k2_zfmisc_1(A_11029,B_11027))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_80875,plain,(
    ! [B_11498,A_11499,A_11500] :
      ( k1_xboole_0 = B_11498
      | v1_funct_2(A_11499,A_11500,B_11498)
      | k1_relset_1(A_11500,B_11498,A_11499) != A_11500
      | ~ r1_tarski(A_11499,k2_zfmisc_1(A_11500,B_11498)) ) ),
    inference(resolution,[status(thm)],[c_22,c_69845])).

tff(c_80887,plain,
    ( k1_xboole_0 = '#skF_7'
    | v1_funct_2('#skF_8','#skF_6','#skF_7')
    | k1_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_80186,c_80875])).

tff(c_80936,plain,
    ( k1_xboole_0 = '#skF_7'
    | v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80102,c_80887])).

tff(c_80937,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_80936])).

tff(c_79991,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_79967])).

tff(c_80037,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_79991])).

tff(c_80046,plain,
    ( ~ v5_relat_1('#skF_8',k1_xboole_0)
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_80037])).

tff(c_80053,plain,(
    ~ v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80046])).

tff(c_80969,plain,(
    ~ v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80937,c_80053])).

tff(c_81054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69545,c_80969])).

tff(c_81055,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_79991])).

tff(c_81069,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_81055,c_20])).

tff(c_81080,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79262,c_81069])).

tff(c_81081,plain,(
    ! [D_11419] : ~ r2_hidden(D_11419,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_79261])).

tff(c_70089,plain,(
    ! [A_11047,B_11048] :
      ( r2_hidden('#skF_3'(A_11047,B_11048),k1_relat_1(A_11047))
      | r2_hidden('#skF_4'(A_11047,B_11048),B_11048)
      | k2_relat_1(A_11047) = B_11048
      | ~ v1_funct_1(A_11047)
      | ~ v1_relat_1(A_11047) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_70110,plain,(
    ! [B_11048] :
      ( r2_hidden('#skF_3'('#skF_8',B_11048),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_11048),B_11048)
      | k2_relat_1('#skF_8') = B_11048
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_70089])).

tff(c_70119,plain,(
    ! [B_11049] :
      ( r2_hidden('#skF_3'('#skF_8',B_11049),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_11049),B_11049)
      | k2_relat_1('#skF_8') = B_11049 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_70110])).

tff(c_70182,plain,(
    ! [B_11051] :
      ( ~ r1_tarski(B_11051,'#skF_4'('#skF_8',B_11051))
      | r2_hidden('#skF_3'('#skF_8',B_11051),'#skF_6')
      | k2_relat_1('#skF_8') = B_11051 ) ),
    inference(resolution,[status(thm)],[c_70119,c_52])).

tff(c_70193,plain,
    ( r2_hidden('#skF_3'('#skF_8',k2_relat_1(k1_xboole_0)),'#skF_6')
    | k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68954,c_70182])).

tff(c_70195,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_70193])).

tff(c_70206,plain,(
    ! [B_10986] : r1_tarski(k2_relat_1('#skF_8'),B_10986) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70195,c_68954])).

tff(c_74043,plain,(
    ! [A_11180,D_11181] :
      ( ~ r1_tarski(k2_relat_1(A_11180),k1_funct_1(A_11180,D_11181))
      | ~ r2_hidden(D_11181,k1_relat_1(A_11180))
      | ~ v1_funct_1(A_11180)
      | ~ v1_relat_1(A_11180) ) ),
    inference(resolution,[status(thm)],[c_68903,c_52])).

tff(c_74053,plain,(
    ! [D_11181] :
      ( ~ r2_hidden(D_11181,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_70206,c_74043])).

tff(c_74133,plain,(
    ! [D_11184] : ~ r2_hidden(D_11184,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_74053])).

tff(c_74171,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_74133])).

tff(c_72624,plain,(
    ! [A_11132,D_11133] :
      ( ~ r1_tarski(k2_relat_1(A_11132),k1_funct_1(A_11132,D_11133))
      | ~ r2_hidden(D_11133,k1_relat_1(A_11132))
      | ~ v1_funct_1(A_11132)
      | ~ v1_relat_1(A_11132) ) ),
    inference(resolution,[status(thm)],[c_68903,c_52])).

tff(c_72637,plain,(
    ! [D_11133] :
      ( ~ r2_hidden(D_11133,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_70206,c_72624])).

tff(c_72667,plain,(
    ! [D_11134] : ~ r2_hidden(D_11134,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_72637])).

tff(c_72705,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_72667])).

tff(c_72714,plain,(
    ! [B_11135] : r1_tarski('#skF_6',B_11135) ),
    inference(resolution,[status(thm)],[c_6,c_72667])).

tff(c_68956,plain,(
    ! [B_10987] : r1_tarski(k2_relat_1(k1_xboole_0),B_10987) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_68938])).

tff(c_69014,plain,(
    ! [B_10987] :
      ( k2_relat_1(k1_xboole_0) = B_10987
      | ~ r1_tarski(B_10987,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_68956,c_8])).

tff(c_70205,plain,(
    ! [B_10987] :
      ( k2_relat_1('#skF_8') = B_10987
      | ~ r1_tarski(B_10987,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70195,c_70195,c_69014])).

tff(c_72763,plain,(
    k2_relat_1('#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_72714,c_70205])).

tff(c_72794,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72763,c_256])).

tff(c_73513,plain,(
    ! [A_11153,C_11154,B_11155,A_11156] :
      ( m1_subset_1(A_11153,k1_zfmisc_1(k2_zfmisc_1(C_11154,B_11155)))
      | ~ r1_tarski(k2_relat_1(A_11153),B_11155)
      | ~ r1_tarski(A_11153,k2_zfmisc_1(C_11154,A_11156)) ) ),
    inference(resolution,[status(thm)],[c_22,c_69553])).

tff(c_73515,plain,(
    ! [B_11155] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_11155)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_11155) ) ),
    inference(resolution,[status(thm)],[c_72794,c_73513])).

tff(c_73696,plain,(
    ! [B_11165] : m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_11165))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72705,c_72763,c_73515])).

tff(c_73707,plain,(
    ! [B_11165] : k1_relset_1('#skF_6',B_11165,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_73696,c_58])).

tff(c_73726,plain,(
    ! [B_11165] : k1_relset_1('#skF_6',B_11165,'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_73707])).

tff(c_73731,plain,(
    ! [B_11165] : r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',B_11165)) ),
    inference(resolution,[status(thm)],[c_73696,c_20])).

tff(c_73836,plain,(
    ! [B_11171,A_11172,A_11173] :
      ( k1_xboole_0 = B_11171
      | v1_funct_2(A_11172,A_11173,B_11171)
      | k1_relset_1(A_11173,B_11171,A_11172) != A_11173
      | ~ r1_tarski(A_11172,k2_zfmisc_1(A_11173,B_11171)) ) ),
    inference(resolution,[status(thm)],[c_22,c_69845])).

tff(c_73839,plain,(
    ! [B_11165] :
      ( k1_xboole_0 = B_11165
      | v1_funct_2('#skF_8','#skF_6',B_11165)
      | k1_relset_1('#skF_6',B_11165,'#skF_8') != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_73731,c_73836])).

tff(c_73976,plain,(
    ! [B_11179] :
      ( k1_xboole_0 = B_11179
      | v1_funct_2('#skF_8','#skF_6',B_11179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73726,c_73839])).

tff(c_73987,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_73976,c_167])).

tff(c_71027,plain,(
    ! [A_11081,D_11082] :
      ( ~ r1_tarski(k2_relat_1(A_11081),k1_funct_1(A_11081,D_11082))
      | ~ r2_hidden(D_11082,k1_relat_1(A_11081))
      | ~ v1_funct_1(A_11081)
      | ~ v1_relat_1(A_11081) ) ),
    inference(resolution,[status(thm)],[c_68903,c_52])).

tff(c_71040,plain,(
    ! [D_11082] :
      ( ~ r2_hidden(D_11082,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_70206,c_71027])).

tff(c_71070,plain,(
    ! [D_11083] : ~ r2_hidden(D_11083,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_71040])).

tff(c_71108,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_71070])).

tff(c_71117,plain,(
    ! [B_11084] : r1_tarski('#skF_6',B_11084) ),
    inference(resolution,[status(thm)],[c_6,c_71070])).

tff(c_71166,plain,(
    k2_relat_1('#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_71117,c_70205])).

tff(c_71197,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71166,c_256])).

tff(c_71917,plain,(
    ! [A_11102,C_11103,B_11104,A_11105] :
      ( m1_subset_1(A_11102,k1_zfmisc_1(k2_zfmisc_1(C_11103,B_11104)))
      | ~ r1_tarski(k2_relat_1(A_11102),B_11104)
      | ~ r1_tarski(A_11102,k2_zfmisc_1(C_11103,A_11105)) ) ),
    inference(resolution,[status(thm)],[c_22,c_69553])).

tff(c_71921,plain,(
    ! [B_11104] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_11104)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_11104) ) ),
    inference(resolution,[status(thm)],[c_71197,c_71917])).

tff(c_72043,plain,(
    ! [B_11110] : m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_11110))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71108,c_71166,c_71921])).

tff(c_72054,plain,(
    ! [B_11110] : k1_relset_1('#skF_6',B_11110,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_72043,c_58])).

tff(c_72073,plain,(
    ! [B_11110] : k1_relset_1('#skF_6',B_11110,'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72054])).

tff(c_72078,plain,(
    ! [B_11110] : r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',B_11110)) ),
    inference(resolution,[status(thm)],[c_72043,c_20])).

tff(c_72275,plain,(
    ! [B_11122,A_11123,A_11124] :
      ( k1_xboole_0 = B_11122
      | v1_funct_2(A_11123,A_11124,B_11122)
      | k1_relset_1(A_11124,B_11122,A_11123) != A_11124
      | ~ r1_tarski(A_11123,k2_zfmisc_1(A_11124,B_11122)) ) ),
    inference(resolution,[status(thm)],[c_22,c_69845])).

tff(c_72278,plain,(
    ! [B_11110] :
      ( k1_xboole_0 = B_11110
      | v1_funct_2('#skF_8','#skF_6',B_11110)
      | k1_relset_1('#skF_6',B_11110,'#skF_8') != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_72078,c_72275])).

tff(c_72319,plain,(
    ! [B_11125] :
      ( k1_xboole_0 = B_11125
      | v1_funct_2('#skF_8','#skF_6',B_11125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72073,c_72278])).

tff(c_72330,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_72319,c_167])).

tff(c_70257,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1('#skF_8')))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_70195,c_32])).

tff(c_70300,plain,(
    r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_70257])).

tff(c_314,plain,(
    ! [C_133,B_134,A_135] :
      ( r2_hidden(C_133,B_134)
      | ~ r2_hidden(C_133,A_135)
      | ~ r1_tarski(A_135,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_330,plain,(
    ! [D_139,B_140] :
      ( r2_hidden(k1_funct_1('#skF_8',D_139),B_140)
      | ~ r1_tarski('#skF_7',B_140)
      | ~ r2_hidden(D_139,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_314])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_336,plain,(
    ! [D_139,B_2,B_140] :
      ( r2_hidden(k1_funct_1('#skF_8',D_139),B_2)
      | ~ r1_tarski(B_140,B_2)
      | ~ r1_tarski('#skF_7',B_140)
      | ~ r2_hidden(D_139,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_330,c_2])).

tff(c_70856,plain,(
    ! [D_139] :
      ( r2_hidden(k1_funct_1('#skF_8',D_139),k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1('#skF_8')))
      | ~ r1_tarski('#skF_7',k1_xboole_0)
      | ~ r2_hidden(D_139,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_70300,c_336])).

tff(c_70868,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_70856])).

tff(c_72342,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72330,c_70868])).

tff(c_72379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_72342])).

tff(c_72381,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_70856])).

tff(c_72395,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(resolution,[status(thm)],[c_72381,c_8])).

tff(c_72397,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_72395])).

tff(c_74002,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73987,c_72397])).

tff(c_74040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_74002])).

tff(c_74041,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_72395])).

tff(c_387,plain,(
    ! [B_148,C_149] :
      ( k1_relset_1(k1_xboole_0,B_148,C_149) = k1_relat_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_375])).

tff(c_393,plain,(
    ! [B_148] : k1_relset_1(k1_xboole_0,B_148,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_347,c_387])).

tff(c_68852,plain,(
    ! [C_10972,B_10973] :
      ( v1_funct_2(C_10972,k1_xboole_0,B_10973)
      | k1_relset_1(k1_xboole_0,B_10973,C_10972) != k1_xboole_0
      | ~ m1_subset_1(C_10972,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_66])).

tff(c_68854,plain,(
    ! [B_10973] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_10973)
      | k1_relset_1(k1_xboole_0,B_10973,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_347,c_68852])).

tff(c_68859,plain,(
    ! [B_10973] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_10973)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_68854])).

tff(c_68861,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_68859])).

tff(c_74088,plain,(
    k1_relat_1('#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74041,c_74041,c_68861])).

tff(c_74113,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74041,c_74041,c_16])).

tff(c_74180,plain,(
    ! [B_11185] : r1_tarski('#skF_6',B_11185) ),
    inference(resolution,[status(thm)],[c_6,c_74133])).

tff(c_74216,plain,(
    k2_relat_1('#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_74180,c_70205])).

tff(c_69564,plain,(
    ! [B_11015] :
      ( k2_relat_1(k1_xboole_0) = k2_relat_1(B_11015)
      | ~ v5_relat_1(B_11015,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(B_11015) ) ),
    inference(resolution,[status(thm)],[c_68956,c_229])).

tff(c_69588,plain,(
    ! [A_132] :
      ( k2_relat_1(k2_zfmisc_1(A_132,k2_relat_1(k1_xboole_0))) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k2_zfmisc_1(A_132,k2_relat_1(k1_xboole_0))) ) ),
    inference(resolution,[status(thm)],[c_313,c_69564])).

tff(c_69616,plain,(
    ! [A_11017] : k2_relat_1(k2_zfmisc_1(A_11017,k2_relat_1(k1_xboole_0))) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_69588])).

tff(c_69668,plain,(
    ! [A_11017,A_12] :
      ( v5_relat_1(k2_zfmisc_1(A_11017,k2_relat_1(k1_xboole_0)),A_12)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),A_12)
      | ~ v1_relat_1(k2_zfmisc_1(A_11017,k2_relat_1(k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69616,c_24])).

tff(c_69708,plain,(
    ! [A_11017,A_12] : v5_relat_1(k2_zfmisc_1(A_11017,k2_relat_1(k1_xboole_0)),A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_68954,c_69668])).

tff(c_70197,plain,(
    ! [A_11017,A_12] : v5_relat_1(k2_zfmisc_1(A_11017,k2_relat_1('#skF_8')),A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70195,c_69708])).

tff(c_74691,plain,(
    ! [A_11196,A_11197] : v5_relat_1(k2_zfmisc_1(A_11196,'#skF_6'),A_11197) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74216,c_70197])).

tff(c_228,plain,(
    ! [B_116,B_95] :
      ( r1_tarski(k2_relat_1(B_116),B_95)
      | ~ v5_relat_1(B_116,'#skF_1'(k2_relat_1(B_116),B_95))
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_212,c_153])).

tff(c_74695,plain,(
    ! [A_11196,B_95] :
      ( r1_tarski(k2_relat_1(k2_zfmisc_1(A_11196,'#skF_6')),B_95)
      | ~ v1_relat_1(k2_zfmisc_1(A_11196,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_74691,c_228])).

tff(c_74930,plain,(
    ! [A_11216,B_11217] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_11216,'#skF_6')),B_11217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_74695])).

tff(c_74224,plain,(
    ! [B_11185] :
      ( B_11185 = '#skF_6'
      | ~ r1_tarski(B_11185,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74180,c_8])).

tff(c_74976,plain,(
    ! [A_11216] : k2_relat_1(k2_zfmisc_1(A_11216,'#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_74930,c_74224])).

tff(c_74994,plain,(
    ! [A_11218] : k2_relat_1(k2_zfmisc_1(A_11218,'#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_74930,c_74224])).

tff(c_75034,plain,(
    ! [A_11218] :
      ( r1_tarski(k2_zfmisc_1(A_11218,'#skF_6'),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_11218,'#skF_6')),'#skF_6'))
      | ~ v1_relat_1(k2_zfmisc_1(A_11218,'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74994,c_32])).

tff(c_76854,plain,(
    ! [A_11325] : r1_tarski(k2_zfmisc_1(A_11325,'#skF_6'),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_11325,'#skF_6')),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_75034])).

tff(c_69561,plain,(
    ! [A_10,C_11011,B_11012,A_11013] :
      ( m1_subset_1(A_10,k1_zfmisc_1(k2_zfmisc_1(C_11011,B_11012)))
      | ~ r1_tarski(k2_relat_1(A_10),B_11012)
      | ~ r1_tarski(A_10,k2_zfmisc_1(C_11011,A_11013)) ) ),
    inference(resolution,[status(thm)],[c_22,c_69553])).

tff(c_76862,plain,(
    ! [A_11325,B_11012] :
      ( m1_subset_1(k2_zfmisc_1(A_11325,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_11325,'#skF_6')),B_11012)))
      | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(A_11325,'#skF_6')),B_11012) ) ),
    inference(resolution,[status(thm)],[c_76854,c_69561])).

tff(c_78111,plain,(
    ! [A_11372,B_11373] : m1_subset_1(k2_zfmisc_1(A_11372,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_11372,'#skF_6')),B_11373))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74171,c_74976,c_76862])).

tff(c_78148,plain,(
    ! [A_11374] : m1_subset_1(k2_zfmisc_1(A_11374,'#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_74113,c_78111])).

tff(c_78168,plain,(
    ! [A_11374] : r1_tarski(k2_zfmisc_1(A_11374,'#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_78148,c_20])).

tff(c_74111,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74041,c_119])).

tff(c_74079,plain,(
    k2_relat_1('#skF_7') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74041,c_70195])).

tff(c_74459,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74216,c_74079])).

tff(c_74775,plain,(
    ! [A_11200] :
      ( k2_zfmisc_1(k1_relat_1(A_11200),k2_relat_1(A_11200)) = A_11200
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_11200),k2_relat_1(A_11200)),A_11200)
      | ~ v1_relat_1(A_11200) ) ),
    inference(resolution,[status(thm)],[c_239,c_8])).

tff(c_74778,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_7'),k2_relat_1('#skF_7')) = '#skF_7'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_7'),'#skF_6'),'#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_74459,c_74775])).

tff(c_74789,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_7'),'#skF_6') = '#skF_7'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_7'),'#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74111,c_74459,c_74778])).

tff(c_77642,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_7'),'#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_74789])).

tff(c_78174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78168,c_77642])).

tff(c_78175,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_7'),'#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_74789])).

tff(c_74110,plain,(
    ! [B_9,A_8] :
      ( B_9 = '#skF_7'
      | A_8 = '#skF_7'
      | k2_zfmisc_1(A_8,B_9) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74041,c_74041,c_74041,c_14])).

tff(c_78207,plain,
    ( '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_78175,c_74110])).

tff(c_78284,plain,(
    '#skF_7' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_74088,c_78207])).

tff(c_69546,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_69533,c_8])).

tff(c_69552,plain,(
    ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_69546])).

tff(c_74236,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74216,c_69552])).

tff(c_78338,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78284,c_74236])).

tff(c_78357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74171,c_78338])).

tff(c_78358,plain,(
    r2_hidden('#skF_3'('#skF_8',k2_relat_1(k1_xboole_0)),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_70193])).

tff(c_81088,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81081,c_78358])).

tff(c_81089,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_69546])).

tff(c_320,plain,(
    ! [D_77,B_134] :
      ( r2_hidden(k1_funct_1('#skF_8',D_77),B_134)
      | ~ r1_tarski('#skF_7',B_134)
      | ~ r2_hidden(D_77,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_314])).

tff(c_579,plain,(
    ! [C_182,A_183,B_184] :
      ( r2_hidden(C_182,A_183)
      | ~ r2_hidden(C_182,k2_relat_1(B_184))
      | ~ v5_relat_1(B_184,A_183)
      | ~ v1_relat_1(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_645,plain,(
    ! [D_192,A_193,B_194] :
      ( r2_hidden(k1_funct_1('#skF_8',D_192),A_193)
      | ~ v5_relat_1(B_194,A_193)
      | ~ v1_relat_1(B_194)
      | ~ r1_tarski('#skF_7',k2_relat_1(B_194))
      | ~ r2_hidden(D_192,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_320,c_579])).

tff(c_671,plain,(
    ! [D_192,B_127,A_10] :
      ( r2_hidden(k1_funct_1('#skF_8',D_192),B_127)
      | ~ v1_relat_1(A_10)
      | ~ r1_tarski('#skF_7',k2_relat_1(A_10))
      | ~ r2_hidden(D_192,'#skF_6')
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_286,c_645])).

tff(c_69074,plain,(
    ! [A_10] :
      ( ~ v1_relat_1(A_10)
      | ~ r1_tarski('#skF_7',k2_relat_1(A_10))
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(splitLeft,[status(thm)],[c_671])).

tff(c_81109,plain,
    ( ~ v1_relat_1('#skF_8')
    | ~ r1_tarski('#skF_7','#skF_7')
    | ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_81089,c_69074])).

tff(c_81159,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_82,c_81109])).

tff(c_81396,plain,(
    ! [B_11521] :
      ( k2_relat_1(k1_xboole_0) = k2_relat_1(B_11521)
      | ~ v5_relat_1(B_11521,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(B_11521) ) ),
    inference(resolution,[status(thm)],[c_68956,c_229])).

tff(c_81424,plain,(
    ! [A_132] :
      ( k2_relat_1(k2_zfmisc_1(A_132,k2_relat_1(k1_xboole_0))) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k2_zfmisc_1(A_132,k2_relat_1(k1_xboole_0))) ) ),
    inference(resolution,[status(thm)],[c_313,c_81396])).

tff(c_81448,plain,(
    ! [A_132] : k2_relat_1(k2_zfmisc_1(A_132,k2_relat_1(k1_xboole_0))) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_81424])).

tff(c_81217,plain,(
    ! [D_11502,C_11503,B_11504,A_11505] :
      ( m1_subset_1(D_11502,k1_zfmisc_1(k2_zfmisc_1(C_11503,B_11504)))
      | ~ r1_tarski(k2_relat_1(D_11502),B_11504)
      | ~ m1_subset_1(D_11502,k1_zfmisc_1(k2_zfmisc_1(C_11503,A_11505))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_83023,plain,(
    ! [A_11603,C_11604,B_11605,A_11606] :
      ( m1_subset_1(A_11603,k1_zfmisc_1(k2_zfmisc_1(C_11604,B_11605)))
      | ~ r1_tarski(k2_relat_1(A_11603),B_11605)
      | ~ r1_tarski(A_11603,k2_zfmisc_1(C_11604,A_11606)) ) ),
    inference(resolution,[status(thm)],[c_22,c_81217])).

tff(c_83297,plain,(
    ! [A_11621,B_11622] :
      ( m1_subset_1(A_11621,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_11621),B_11622)))
      | ~ r1_tarski(k2_relat_1(A_11621),B_11622)
      | ~ v1_relat_1(A_11621) ) ),
    inference(resolution,[status(thm)],[c_32,c_83023])).

tff(c_83334,plain,(
    ! [A_11623] :
      ( m1_subset_1(A_11623,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(A_11623),k1_xboole_0)
      | ~ v1_relat_1(A_11623) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_83297])).

tff(c_83337,plain,(
    ! [A_132] :
      ( m1_subset_1(k2_zfmisc_1(A_132,k2_relat_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
      | ~ v1_relat_1(k2_zfmisc_1(A_132,k2_relat_1(k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81448,c_83334])).

tff(c_83367,plain,(
    ! [A_11624] : m1_subset_1(k2_zfmisc_1(A_11624,k2_relat_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_68954,c_83337])).

tff(c_83445,plain,(
    ! [A_11630] : r1_tarski(k2_zfmisc_1(A_11630,k2_relat_1(k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_83367,c_20])).

tff(c_254,plain,(
    ! [A_121] :
      ( k2_zfmisc_1(k1_relat_1(A_121),k2_relat_1(A_121)) = A_121
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_121),k2_relat_1(A_121)),A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(resolution,[status(thm)],[c_239,c_8])).

tff(c_83449,plain,
    ( k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_83445,c_254])).

tff(c_83473,plain,(
    k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_83449])).

tff(c_83567,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_83473,c_14])).

tff(c_83591,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68861,c_83567])).

tff(c_81754,plain,(
    ! [A_11534,B_11535] :
      ( r2_hidden('#skF_3'(A_11534,B_11535),k1_relat_1(A_11534))
      | r2_hidden('#skF_4'(A_11534,B_11535),B_11535)
      | k2_relat_1(A_11534) = B_11535
      | ~ v1_funct_1(A_11534)
      | ~ v1_relat_1(A_11534) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_81772,plain,(
    ! [B_11535] :
      ( r2_hidden('#skF_3'('#skF_8',B_11535),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_11535),B_11535)
      | k2_relat_1('#skF_8') = B_11535
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_81754])).

tff(c_81809,plain,(
    ! [B_11538] :
      ( r2_hidden('#skF_3'('#skF_8',B_11538),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_11538),B_11538)
      | B_11538 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_81089,c_81772])).

tff(c_81973,plain,(
    ! [B_11548] :
      ( ~ r1_tarski(B_11548,'#skF_4'('#skF_8',B_11548))
      | r2_hidden('#skF_3'('#skF_8',B_11548),'#skF_6')
      | B_11548 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_81809,c_52])).

tff(c_81984,plain,
    ( r2_hidden('#skF_3'('#skF_8',k2_relat_1(k1_xboole_0)),'#skF_6')
    | k2_relat_1(k1_xboole_0) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_68954,c_81973])).

tff(c_81986,plain,(
    k2_relat_1(k1_xboole_0) = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_81984])).

tff(c_30,plain,(
    ! [C_19,A_16,B_17] :
      ( r2_hidden(C_19,A_16)
      | ~ r2_hidden(C_19,k2_relat_1(B_17))
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_81132,plain,(
    ! [C_19,A_16] :
      ( r2_hidden(C_19,A_16)
      | ~ r2_hidden(C_19,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_16)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81089,c_30])).

tff(c_81336,plain,(
    ! [C_11514,A_11515] :
      ( r2_hidden(C_11514,A_11515)
      | ~ r2_hidden(C_11514,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_11515) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_81132])).

tff(c_81367,plain,(
    ! [D_11519,A_11520] :
      ( r2_hidden(k1_funct_1('#skF_8',D_11519),A_11520)
      | ~ v5_relat_1('#skF_8',A_11520)
      | ~ r2_hidden(D_11519,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_81336])).

tff(c_81661,plain,(
    ! [A_11530,D_11531] :
      ( ~ r1_tarski(A_11530,k1_funct_1('#skF_8',D_11531))
      | ~ v5_relat_1('#skF_8',A_11530)
      | ~ r2_hidden(D_11531,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_81367,c_52])).

tff(c_81685,plain,(
    ! [D_11531] :
      ( ~ v5_relat_1('#skF_8',k2_relat_1(k1_xboole_0))
      | ~ r2_hidden(D_11531,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_68954,c_81661])).

tff(c_81688,plain,(
    ~ v5_relat_1('#skF_8',k2_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_81685])).

tff(c_81987,plain,(
    ~ v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81986,c_81688])).

tff(c_82005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69545,c_81987])).

tff(c_82007,plain,(
    k2_relat_1(k1_xboole_0) != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_81984])).

tff(c_83614,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83591,c_82007])).

tff(c_456,plain,(
    ! [A_160,B_161,A_162] :
      ( k1_relset_1(A_160,B_161,A_162) = k1_relat_1(A_162)
      | ~ r1_tarski(A_162,k2_zfmisc_1(A_160,B_161)) ) ),
    inference(resolution,[status(thm)],[c_22,c_375])).

tff(c_459,plain,(
    k1_relset_1('#skF_6',k2_relat_1('#skF_8'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_256,c_456])).

tff(c_478,plain,(
    k1_relset_1('#skF_6',k2_relat_1('#skF_8'),'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_459])).

tff(c_81097,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81089,c_478])).

tff(c_81100,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81089,c_256])).

tff(c_81354,plain,(
    ! [B_11516,C_11517,A_11518] :
      ( k1_xboole_0 = B_11516
      | v1_funct_2(C_11517,A_11518,B_11516)
      | k1_relset_1(A_11518,B_11516,C_11517) != A_11518
      | ~ m1_subset_1(C_11517,k1_zfmisc_1(k2_zfmisc_1(A_11518,B_11516))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_83892,plain,(
    ! [B_11632,A_11633,A_11634] :
      ( k1_xboole_0 = B_11632
      | v1_funct_2(A_11633,A_11634,B_11632)
      | k1_relset_1(A_11634,B_11632,A_11633) != A_11634
      | ~ r1_tarski(A_11633,k2_zfmisc_1(A_11634,B_11632)) ) ),
    inference(resolution,[status(thm)],[c_22,c_81354])).

tff(c_83906,plain,
    ( k1_xboole_0 = '#skF_7'
    | v1_funct_2('#skF_8','#skF_6','#skF_7')
    | k1_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_81100,c_83892])).

tff(c_83933,plain,
    ( k1_xboole_0 = '#skF_7'
    | v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81097,c_83906])).

tff(c_83935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_83614,c_83933])).

tff(c_83936,plain,(
    ! [D_11531] : ~ r2_hidden(D_11531,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_81685])).

tff(c_69483,plain,(
    ! [C_11006] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_11006),'#skF_6')
      | ~ r2_hidden(C_11006,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_69477])).

tff(c_81096,plain,(
    ! [C_11006] :
      ( r2_hidden('#skF_5'('#skF_8','#skF_7',C_11006),'#skF_6')
      | ~ r2_hidden(C_11006,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81089,c_81089,c_69483])).

tff(c_83950,plain,(
    ! [C_11636] : ~ r2_hidden(C_11636,'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_83936,c_81096])).

tff(c_83960,plain,(
    ! [B_2] : r1_tarski('#skF_7',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_83950])).

tff(c_81153,plain,(
    ! [A_12] :
      ( v5_relat_1('#skF_8',A_12)
      | ~ r1_tarski('#skF_7',A_12)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81089,c_24])).

tff(c_81242,plain,(
    ! [A_11507] :
      ( v5_relat_1('#skF_8',A_11507)
      | ~ r1_tarski('#skF_7',A_11507) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_81153])).

tff(c_168,plain,(
    ! [C_101,A_102,B_103] :
      ( v4_relat_1(C_101,A_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_179,plain,(
    ! [A_10,A_102,B_103] :
      ( v4_relat_1(A_10,A_102)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_102,B_103)) ) ),
    inference(resolution,[status(thm)],[c_22,c_168])).

tff(c_524,plain,(
    ! [B_168,A_169,B_170] :
      ( v4_relat_1(k2_relat_1(B_168),A_169)
      | ~ v5_relat_1(B_168,k2_zfmisc_1(A_169,B_170))
      | ~ v1_relat_1(B_168) ) ),
    inference(resolution,[status(thm)],[c_212,c_179])).

tff(c_542,plain,(
    ! [B_168,A_8] :
      ( v4_relat_1(k2_relat_1(B_168),A_8)
      | ~ v5_relat_1(B_168,k1_xboole_0)
      | ~ v1_relat_1(B_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_524])).

tff(c_81138,plain,(
    ! [A_8] :
      ( v4_relat_1('#skF_7',A_8)
      | ~ v5_relat_1('#skF_8',k1_xboole_0)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81089,c_542])).

tff(c_81179,plain,(
    ! [A_8] :
      ( v4_relat_1('#skF_7',A_8)
      | ~ v5_relat_1('#skF_8',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_81138])).

tff(c_81237,plain,(
    ~ v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_81179])).

tff(c_81263,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_81242,c_81237])).

tff(c_83973,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83960,c_81263])).

tff(c_83975,plain,(
    v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_81179])).

tff(c_81147,plain,(
    ! [A_12] :
      ( r1_tarski('#skF_7',A_12)
      | ~ v5_relat_1('#skF_8',A_12)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81089,c_26])).

tff(c_84015,plain,(
    ! [A_11639] :
      ( r1_tarski('#skF_7',A_11639)
      | ~ v5_relat_1('#skF_8',A_11639) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_81147])).

tff(c_84034,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_83975,c_84015])).

tff(c_85679,plain,(
    ! [A_11738,C_11739,B_11740,A_11741] :
      ( m1_subset_1(A_11738,k1_zfmisc_1(k2_zfmisc_1(C_11739,B_11740)))
      | ~ r1_tarski(k2_relat_1(A_11738),B_11740)
      | ~ r1_tarski(A_11738,k2_zfmisc_1(C_11739,A_11741)) ) ),
    inference(resolution,[status(thm)],[c_22,c_81217])).

tff(c_85681,plain,(
    ! [B_11740] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_11740)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_11740) ) ),
    inference(resolution,[status(thm)],[c_81100,c_85679])).

tff(c_85824,plain,(
    ! [B_11747] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_11747)))
      | ~ r1_tarski('#skF_7',B_11747) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81089,c_85681])).

tff(c_85848,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_85824])).

tff(c_85860,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84034,c_85848])).

tff(c_85873,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_85860,c_20])).

tff(c_85884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81159,c_85873])).

tff(c_86118,plain,(
    ! [D_11757,B_11758] :
      ( r2_hidden(k1_funct_1('#skF_8',D_11757),B_11758)
      | ~ r2_hidden(D_11757,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_671])).

tff(c_86134,plain,(
    ! [B_11759,D_11760] :
      ( ~ r1_tarski(B_11759,k1_funct_1('#skF_8',D_11760))
      | ~ r2_hidden(D_11760,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_86118,c_52])).

tff(c_86149,plain,(
    ! [D_11761] : ~ r2_hidden(D_11761,'#skF_6') ),
    inference(resolution,[status(thm)],[c_68954,c_86134])).

tff(c_86159,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_86149])).

tff(c_86145,plain,(
    ! [D_11760] : ~ r2_hidden(D_11760,'#skF_6') ),
    inference(resolution,[status(thm)],[c_68954,c_86134])).

tff(c_85973,plain,(
    ! [A_11750,C_11751] :
      ( r2_hidden('#skF_5'(A_11750,k2_relat_1(A_11750),C_11751),k1_relat_1(A_11750))
      | ~ r2_hidden(C_11751,k2_relat_1(A_11750))
      | ~ v1_funct_1(A_11750)
      | ~ v1_relat_1(A_11750) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_85981,plain,(
    ! [C_11751] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_11751),'#skF_6')
      | ~ r2_hidden(C_11751,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_85973])).

tff(c_85985,plain,(
    ! [C_11751] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_11751),'#skF_6')
      | ~ r2_hidden(C_11751,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_85981])).

tff(c_86307,plain,(
    ! [C_11767] : ~ r2_hidden(C_11767,k2_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_86145,c_85985])).

tff(c_86324,plain,(
    ! [B_2] : r1_tarski(k2_relat_1('#skF_8'),B_2) ),
    inference(resolution,[status(thm)],[c_6,c_86307])).

tff(c_86170,plain,(
    ! [B_11766] : r1_tarski('#skF_6',B_11766) ),
    inference(resolution,[status(thm)],[c_6,c_86149])).

tff(c_86545,plain,(
    ! [B_11778] :
      ( B_11778 = '#skF_6'
      | ~ r1_tarski(B_11778,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_86170,c_8])).

tff(c_86562,plain,(
    k2_relat_1('#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_86324,c_86545])).

tff(c_86574,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86562,c_256])).

tff(c_86160,plain,(
    ! [D_11762,C_11763,B_11764,A_11765] :
      ( m1_subset_1(D_11762,k1_zfmisc_1(k2_zfmisc_1(C_11763,B_11764)))
      | ~ r1_tarski(k2_relat_1(D_11762),B_11764)
      | ~ m1_subset_1(D_11762,k1_zfmisc_1(k2_zfmisc_1(C_11763,A_11765))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_88527,plain,(
    ! [A_11870,C_11871,B_11872,A_11873] :
      ( m1_subset_1(A_11870,k1_zfmisc_1(k2_zfmisc_1(C_11871,B_11872)))
      | ~ r1_tarski(k2_relat_1(A_11870),B_11872)
      | ~ r1_tarski(A_11870,k2_zfmisc_1(C_11871,A_11873)) ) ),
    inference(resolution,[status(thm)],[c_22,c_86160])).

tff(c_88548,plain,(
    ! [B_11872] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_11872)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_11872) ) ),
    inference(resolution,[status(thm)],[c_86574,c_88527])).

tff(c_88653,plain,(
    ! [B_11876] : m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_11876))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86159,c_86562,c_88548])).

tff(c_88664,plain,(
    ! [B_11876] : k1_relset_1('#skF_6',B_11876,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_88653,c_58])).

tff(c_88683,plain,(
    ! [B_11876] : k1_relset_1('#skF_6',B_11876,'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_88664])).

tff(c_88677,plain,(
    ! [B_11876] :
      ( k1_xboole_0 = B_11876
      | v1_funct_2('#skF_8','#skF_6',B_11876)
      | k1_relset_1('#skF_6',B_11876,'#skF_8') != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_88653,c_68])).

tff(c_89164,plain,(
    ! [B_11900] :
      ( k1_xboole_0 = B_11900
      | v1_funct_2('#skF_8','#skF_6',B_11900) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88683,c_88677])).

tff(c_89176,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_89164,c_167])).

tff(c_89232,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89176,c_89176,c_16])).

tff(c_86899,plain,(
    ! [B_11800] :
      ( k2_relat_1(B_11800) = '#skF_6'
      | ~ v5_relat_1(B_11800,'#skF_6')
      | ~ v1_relat_1(B_11800) ) ),
    inference(resolution,[status(thm)],[c_86170,c_229])).

tff(c_86927,plain,(
    ! [A_132] :
      ( k2_relat_1(k2_zfmisc_1(A_132,'#skF_6')) = '#skF_6'
      | ~ v1_relat_1(k2_zfmisc_1(A_132,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_313,c_86899])).

tff(c_86946,plain,(
    ! [A_132] : k2_relat_1(k2_zfmisc_1(A_132,'#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_86927])).

tff(c_86948,plain,(
    ! [A_11801] : k2_relat_1(k2_zfmisc_1(A_11801,'#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_86927])).

tff(c_86985,plain,(
    ! [A_11801] :
      ( r1_tarski(k2_zfmisc_1(A_11801,'#skF_6'),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_11801,'#skF_6')),'#skF_6'))
      | ~ v1_relat_1(k2_zfmisc_1(A_11801,'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86948,c_32])).

tff(c_87025,plain,(
    ! [A_11801] : r1_tarski(k2_zfmisc_1(A_11801,'#skF_6'),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_11801,'#skF_6')),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_86985])).

tff(c_88538,plain,(
    ! [A_11801,B_11872] :
      ( m1_subset_1(k2_zfmisc_1(A_11801,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_11801,'#skF_6')),B_11872)))
      | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(A_11801,'#skF_6')),B_11872) ) ),
    inference(resolution,[status(thm)],[c_87025,c_88527])).

tff(c_91102,plain,(
    ! [A_11991,B_11992] : m1_subset_1(k2_zfmisc_1(A_11991,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_11991,'#skF_6')),B_11992))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86159,c_86946,c_88538])).

tff(c_91139,plain,(
    ! [A_11993] : m1_subset_1(k2_zfmisc_1(A_11993,'#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_89232,c_91102])).

tff(c_91159,plain,(
    ! [A_11993] : r1_tarski(k2_zfmisc_1(A_11993,'#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_91139,c_20])).

tff(c_86212,plain,(
    k2_relat_1(k1_xboole_0) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_86170,c_69014])).

tff(c_86265,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),'#skF_6'))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_86212,c_32])).

tff(c_86299,plain,(
    r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_86265])).

tff(c_86816,plain,
    ( k2_zfmisc_1(k1_relat_1(k1_xboole_0),'#skF_6') = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),'#skF_6'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_86299,c_8])).

tff(c_87718,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),'#skF_6'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_86816])).

tff(c_89198,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_7'),'#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89176,c_89176,c_87718])).

tff(c_91169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91159,c_89198])).

tff(c_91170,plain,(
    k2_zfmisc_1(k1_relat_1(k1_xboole_0),'#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_86816])).

tff(c_91257,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_91170,c_14])).

tff(c_91280,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_68861,c_91257])).

tff(c_91318,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91280,c_91280,c_16])).

tff(c_263,plain,
    ( k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8')) = '#skF_8'
    | ~ r1_tarski(k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_256,c_8])).

tff(c_287,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8')),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_86573,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86562,c_287])).

tff(c_91376,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91318,c_86573])).

tff(c_91385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86159,c_91376])).

tff(c_91387,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_68859])).

tff(c_34,plain,(
    ! [A_21,D_60] :
      ( r2_hidden(k1_funct_1(A_21,D_60),k2_relat_1(A_21))
      | ~ r2_hidden(D_60,k1_relat_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_31187,plain,(
    ! [A_5911,C_5912] :
      ( r2_hidden('#skF_5'(A_5911,k2_relat_1(A_5911),C_5912),k1_relat_1(A_5911))
      | ~ r2_hidden(C_5912,k2_relat_1(A_5911))
      | ~ v1_funct_1(A_5911)
      | ~ v1_relat_1(A_5911) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_31198,plain,(
    ! [C_5912] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_5912),'#skF_6')
      | ~ r2_hidden(C_5912,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_31187])).

tff(c_31204,plain,(
    ! [C_5912] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_5912),'#skF_6')
      | ~ r2_hidden(C_5912,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_31198])).

tff(c_31524,plain,(
    ! [A_5924,C_5925] :
      ( k1_funct_1(A_5924,'#skF_5'(A_5924,k2_relat_1(A_5924),C_5925)) = C_5925
      | ~ r2_hidden(C_5925,k2_relat_1(A_5924))
      | ~ v1_funct_1(A_5924)
      | ~ v1_relat_1(A_5924) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_31554,plain,(
    ! [C_5925] :
      ( r2_hidden(C_5925,'#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_5925),'#skF_6')
      | ~ r2_hidden(C_5925,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31524,c_76])).

tff(c_31608,plain,(
    ! [C_5931] :
      ( r2_hidden(C_5931,'#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_5931),'#skF_6')
      | ~ r2_hidden(C_5931,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_31554])).

tff(c_31613,plain,(
    ! [C_5932] :
      ( r2_hidden(C_5932,'#skF_7')
      | ~ r2_hidden(C_5932,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_31204,c_31608])).

tff(c_31636,plain,(
    ! [B_5933] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_8'),B_5933),'#skF_7')
      | r1_tarski(k2_relat_1('#skF_8'),B_5933) ) ),
    inference(resolution,[status(thm)],[c_6,c_31613])).

tff(c_31647,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_31636,c_4])).

tff(c_32047,plain,(
    ! [B_5965,B_5966] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_8'),B_5965),B_5966)
      | ~ r1_tarski('#skF_7',B_5966)
      | r1_tarski(k2_relat_1('#skF_8'),B_5965) ) ),
    inference(resolution,[status(thm)],[c_31636,c_2])).

tff(c_32096,plain,(
    ! [B_5969] :
      ( ~ r1_tarski('#skF_7',B_5969)
      | r1_tarski(k2_relat_1('#skF_8'),B_5969) ) ),
    inference(resolution,[status(thm)],[c_32047,c_4])).

tff(c_275,plain,(
    ! [A_10,B_123,A_124] :
      ( v5_relat_1(A_10,B_123)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_124,B_123)) ) ),
    inference(resolution,[status(thm)],[c_22,c_264])).

tff(c_32234,plain,(
    ! [B_5971,A_5972] :
      ( v5_relat_1(k2_relat_1('#skF_8'),B_5971)
      | ~ r1_tarski('#skF_7',k2_zfmisc_1(A_5972,B_5971)) ) ),
    inference(resolution,[status(thm)],[c_32096,c_275])).

tff(c_32242,plain,
    ( v5_relat_1(k2_relat_1('#skF_8'),k2_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_32234])).

tff(c_32243,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_32242])).

tff(c_780,plain,(
    ! [B_211,B_212] :
      ( r1_tarski(k2_relat_1(B_211),B_212)
      | ~ v5_relat_1(B_211,'#skF_1'(k2_relat_1(B_211),B_212))
      | ~ v1_relat_1(B_211) ) ),
    inference(resolution,[status(thm)],[c_212,c_153])).

tff(c_807,plain,(
    ! [A_10,B_212] :
      ( r1_tarski(k2_relat_1(A_10),B_212)
      | ~ v1_relat_1(A_10)
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_286,c_780])).

tff(c_31101,plain,(
    ! [A_5902,D_5903] :
      ( r2_hidden(k1_funct_1(A_5902,D_5903),k2_relat_1(A_5902))
      | ~ r2_hidden(D_5903,k1_relat_1(A_5902))
      | ~ v1_funct_1(A_5902)
      | ~ v1_relat_1(A_5902) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_40069,plain,(
    ! [A_6304,D_6305] :
      ( ~ r1_tarski(k2_relat_1(A_6304),k1_funct_1(A_6304,D_6305))
      | ~ r2_hidden(D_6305,k1_relat_1(A_6304))
      | ~ v1_funct_1(A_6304)
      | ~ v1_relat_1(A_6304) ) ),
    inference(resolution,[status(thm)],[c_31101,c_52])).

tff(c_40110,plain,(
    ! [D_6306,A_6307] :
      ( ~ r2_hidden(D_6306,k1_relat_1(A_6307))
      | ~ v1_funct_1(A_6307)
      | ~ v1_relat_1(A_6307)
      | ~ r1_tarski(A_6307,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_807,c_40069])).

tff(c_40178,plain,(
    ! [D_6306] :
      ( ~ r2_hidden(D_6306,'#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_40110])).

tff(c_40198,plain,(
    ! [D_6306] :
      ( ~ r2_hidden(D_6306,'#skF_6')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_40178])).

tff(c_40199,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_40198])).

tff(c_35185,plain,(
    ! [A_6103,D_6104] :
      ( ~ r1_tarski(k2_relat_1(A_6103),k1_funct_1(A_6103,D_6104))
      | ~ r2_hidden(D_6104,k1_relat_1(A_6103))
      | ~ v1_funct_1(A_6103)
      | ~ v1_relat_1(A_6103) ) ),
    inference(resolution,[status(thm)],[c_31101,c_52])).

tff(c_35231,plain,(
    ! [D_6105,A_6106] :
      ( ~ r2_hidden(D_6105,k1_relat_1(A_6106))
      | ~ v1_funct_1(A_6106)
      | ~ v1_relat_1(A_6106)
      | ~ r1_tarski(A_6106,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_807,c_35185])).

tff(c_35295,plain,(
    ! [D_6105] :
      ( ~ r2_hidden(D_6105,'#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_35231])).

tff(c_35314,plain,(
    ! [D_6105] :
      ( ~ r2_hidden(D_6105,'#skF_6')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_35295])).

tff(c_35315,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_35314])).

tff(c_31653,plain,
    ( v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_31647,c_24])).

tff(c_31659,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_31653])).

tff(c_31667,plain,(
    ! [D_5934,C_5935,B_5936,A_5937] :
      ( m1_subset_1(D_5934,k1_zfmisc_1(k2_zfmisc_1(C_5935,B_5936)))
      | ~ r1_tarski(k2_relat_1(D_5934),B_5936)
      | ~ m1_subset_1(D_5934,k1_zfmisc_1(k2_zfmisc_1(C_5935,A_5937))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36278,plain,(
    ! [A_6153,C_6154,B_6155,A_6156] :
      ( m1_subset_1(A_6153,k1_zfmisc_1(k2_zfmisc_1(C_6154,B_6155)))
      | ~ r1_tarski(k2_relat_1(A_6153),B_6155)
      | ~ r1_tarski(A_6153,k2_zfmisc_1(C_6154,A_6156)) ) ),
    inference(resolution,[status(thm)],[c_22,c_31667])).

tff(c_36415,plain,(
    ! [B_6163] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_6163)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_6163) ) ),
    inference(resolution,[status(thm)],[c_256,c_36278])).

tff(c_36426,plain,(
    ! [B_6163] :
      ( k1_relset_1('#skF_6',B_6163,'#skF_8') = k1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_6163) ) ),
    inference(resolution,[status(thm)],[c_36415,c_58])).

tff(c_36514,plain,(
    ! [B_6165] :
      ( k1_relset_1('#skF_6',B_6165,'#skF_8') = '#skF_6'
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_6165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_36426])).

tff(c_36543,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_31647,c_36514])).

tff(c_36682,plain,(
    ! [B_6171] :
      ( r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',B_6171))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_6171) ) ),
    inference(resolution,[status(thm)],[c_36415,c_20])).

tff(c_36711,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_31647,c_36682])).

tff(c_32244,plain,(
    ! [B_5973,C_5974,A_5975] :
      ( k1_xboole_0 = B_5973
      | v1_funct_2(C_5974,A_5975,B_5973)
      | k1_relset_1(A_5975,B_5973,C_5974) != A_5975
      | ~ m1_subset_1(C_5974,k1_zfmisc_1(k2_zfmisc_1(A_5975,B_5973))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_32255,plain,(
    ! [B_5973,A_10,A_5975] :
      ( k1_xboole_0 = B_5973
      | v1_funct_2(A_10,A_5975,B_5973)
      | k1_relset_1(A_5975,B_5973,A_10) != A_5975
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_5975,B_5973)) ) ),
    inference(resolution,[status(thm)],[c_22,c_32244])).

tff(c_36723,plain,
    ( k1_xboole_0 = '#skF_7'
    | v1_funct_2('#skF_8','#skF_6','#skF_7')
    | k1_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_36711,c_32255])).

tff(c_36743,plain,
    ( k1_xboole_0 = '#skF_7'
    | v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36543,c_36723])).

tff(c_36744,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_36743])).

tff(c_35567,plain,(
    ! [D_6113,A_6114,B_6115] :
      ( m1_subset_1(D_6113,k1_zfmisc_1(k2_zfmisc_1(A_6114,B_6115)))
      | ~ r1_tarski(k2_relat_1(D_6113),B_6115)
      | ~ m1_subset_1(D_6113,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_31667])).

tff(c_35786,plain,(
    ! [D_6125,A_6126,B_6127] :
      ( r1_tarski(D_6125,k2_zfmisc_1(A_6126,B_6127))
      | ~ r1_tarski(k2_relat_1(D_6125),B_6127)
      | ~ m1_subset_1(D_6125,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_35567,c_20])).

tff(c_35815,plain,(
    ! [A_6126] :
      ( r1_tarski('#skF_8',k2_zfmisc_1(A_6126,'#skF_7'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_31647,c_35786])).

tff(c_35877,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_35815])).

tff(c_36439,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_36415])).

tff(c_36449,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_35877,c_36439])).

tff(c_36458,plain,
    ( ~ v5_relat_1('#skF_8',k1_xboole_0)
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_36449])).

tff(c_36465,plain,(
    ~ v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_36458])).

tff(c_36756,plain,(
    ~ v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36744,c_36465])).

tff(c_36856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31659,c_36756])).

tff(c_36858,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_35815])).

tff(c_36913,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36858,c_20])).

tff(c_36924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35315,c_36913])).

tff(c_36925,plain,(
    ! [D_6105] : ~ r2_hidden(D_6105,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_35314])).

tff(c_796,plain,(
    ! [B_212] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),B_212)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_324,c_780])).

tff(c_806,plain,(
    ! [B_212] : r1_tarski(k2_relat_1(k1_xboole_0),B_212) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_796])).

tff(c_32293,plain,(
    ! [A_5979,B_5980] :
      ( r2_hidden('#skF_3'(A_5979,B_5980),k1_relat_1(A_5979))
      | r2_hidden('#skF_4'(A_5979,B_5980),B_5980)
      | k2_relat_1(A_5979) = B_5980
      | ~ v1_funct_1(A_5979)
      | ~ v1_relat_1(A_5979) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32316,plain,(
    ! [B_5980] :
      ( r2_hidden('#skF_3'('#skF_8',B_5980),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_5980),B_5980)
      | k2_relat_1('#skF_8') = B_5980
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_32293])).

tff(c_32326,plain,(
    ! [B_5981] :
      ( r2_hidden('#skF_3'('#skF_8',B_5981),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_5981),B_5981)
      | k2_relat_1('#skF_8') = B_5981 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_32316])).

tff(c_32381,plain,(
    ! [B_5983] :
      ( ~ r1_tarski(B_5983,'#skF_4'('#skF_8',B_5983))
      | r2_hidden('#skF_3'('#skF_8',B_5983),'#skF_6')
      | k2_relat_1('#skF_8') = B_5983 ) ),
    inference(resolution,[status(thm)],[c_32326,c_52])).

tff(c_32397,plain,
    ( r2_hidden('#skF_3'('#skF_8',k2_relat_1(k1_xboole_0)),'#skF_6')
    | k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_806,c_32381])).

tff(c_32399,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_32397])).

tff(c_32408,plain,(
    ! [B_212] : r1_tarski(k2_relat_1('#skF_8'),B_212) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32399,c_806])).

tff(c_32459,plain,(
    ! [C_19,A_16] :
      ( r2_hidden(C_19,A_16)
      | ~ r2_hidden(C_19,k2_relat_1('#skF_8'))
      | ~ v5_relat_1(k1_xboole_0,A_16)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32399,c_30])).

tff(c_32915,plain,(
    ! [C_6005,A_6006] :
      ( r2_hidden(C_6005,A_6006)
      | ~ r2_hidden(C_6005,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_324,c_32459])).

tff(c_32940,plain,(
    ! [D_60,A_6006] :
      ( r2_hidden(k1_funct_1('#skF_8',D_60),A_6006)
      | ~ r2_hidden(D_60,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_32915])).

tff(c_33210,plain,(
    ! [D_6014,A_6015] :
      ( r2_hidden(k1_funct_1('#skF_8',D_6014),A_6015)
      | ~ r2_hidden(D_6014,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_32940])).

tff(c_33241,plain,(
    ! [A_6016,D_6017] :
      ( ~ r1_tarski(A_6016,k1_funct_1('#skF_8',D_6017))
      | ~ r2_hidden(D_6017,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_33210,c_52])).

tff(c_33271,plain,(
    ! [D_6018] : ~ r2_hidden(D_6018,'#skF_6') ),
    inference(resolution,[status(thm)],[c_32408,c_33241])).

tff(c_33309,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_33271])).

tff(c_33357,plain,(
    ! [B_6020] : r1_tarski('#skF_6',B_6020) ),
    inference(resolution,[status(thm)],[c_6,c_33271])).

tff(c_808,plain,(
    ! [B_213] : r1_tarski(k2_relat_1(k1_xboole_0),B_213) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_796])).

tff(c_866,plain,(
    ! [B_213] :
      ( k2_relat_1(k1_xboole_0) = B_213
      | ~ r1_tarski(B_213,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_808,c_8])).

tff(c_32407,plain,(
    ! [B_213] :
      ( k2_relat_1('#skF_8') = B_213
      | ~ r1_tarski(B_213,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32399,c_32399,c_866])).

tff(c_33406,plain,(
    k2_relat_1('#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_33357,c_32407])).

tff(c_33435,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33406,c_256])).

tff(c_34130,plain,(
    ! [A_6043,C_6044,B_6045,A_6046] :
      ( m1_subset_1(A_6043,k1_zfmisc_1(k2_zfmisc_1(C_6044,B_6045)))
      | ~ r1_tarski(k2_relat_1(A_6043),B_6045)
      | ~ r1_tarski(A_6043,k2_zfmisc_1(C_6044,A_6046)) ) ),
    inference(resolution,[status(thm)],[c_22,c_31667])).

tff(c_34132,plain,(
    ! [B_6045] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_6045)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_6045) ) ),
    inference(resolution,[status(thm)],[c_33435,c_34130])).

tff(c_34162,plain,(
    ! [B_6047] : m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_6047))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33309,c_33406,c_34132])).

tff(c_34173,plain,(
    ! [B_6047] : k1_relset_1('#skF_6',B_6047,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34162,c_58])).

tff(c_34192,plain,(
    ! [B_6047] : k1_relset_1('#skF_6',B_6047,'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_34173])).

tff(c_34197,plain,(
    ! [B_6047] : r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',B_6047)) ),
    inference(resolution,[status(thm)],[c_34162,c_20])).

tff(c_34331,plain,(
    ! [B_6054,A_6055,A_6056] :
      ( k1_xboole_0 = B_6054
      | v1_funct_2(A_6055,A_6056,B_6054)
      | k1_relset_1(A_6056,B_6054,A_6055) != A_6056
      | ~ r1_tarski(A_6055,k2_zfmisc_1(A_6056,B_6054)) ) ),
    inference(resolution,[status(thm)],[c_22,c_32244])).

tff(c_34334,plain,(
    ! [B_6047] :
      ( k1_xboole_0 = B_6047
      | v1_funct_2('#skF_8','#skF_6',B_6047)
      | k1_relset_1('#skF_6',B_6047,'#skF_8') != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_34197,c_34331])).

tff(c_34377,plain,(
    ! [B_6057] :
      ( k1_xboole_0 = B_6057
      | v1_funct_2('#skF_8','#skF_6',B_6057) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34192,c_34334])).

tff(c_34388,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_34377,c_167])).

tff(c_32239,plain,(
    ! [B_9] :
      ( v5_relat_1(k2_relat_1('#skF_8'),B_9)
      | ~ r1_tarski('#skF_7',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_32234])).

tff(c_32257,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_32239])).

tff(c_34398,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34388,c_32257])).

tff(c_34440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34398])).

tff(c_34441,plain,(
    r2_hidden('#skF_3'('#skF_8',k2_relat_1(k1_xboole_0)),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_32397])).

tff(c_36932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36925,c_34441])).

tff(c_36934,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_32239])).

tff(c_32072,plain,(
    ! [B_5966] :
      ( ~ r1_tarski('#skF_7',B_5966)
      | r1_tarski(k2_relat_1('#skF_8'),B_5966) ) ),
    inference(resolution,[status(thm)],[c_32047,c_4])).

tff(c_40457,plain,(
    ! [D_6314,A_6315,B_6316] :
      ( m1_subset_1(D_6314,k1_zfmisc_1(k2_zfmisc_1(A_6315,B_6316)))
      | ~ r1_tarski(k2_relat_1(D_6314),B_6316)
      | ~ m1_subset_1(D_6314,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_31667])).

tff(c_40702,plain,(
    ! [D_6328,A_6329,B_6330] :
      ( r1_tarski(D_6328,k2_zfmisc_1(A_6329,B_6330))
      | ~ r1_tarski(k2_relat_1(D_6328),B_6330)
      | ~ m1_subset_1(D_6328,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_40457,c_20])).

tff(c_40728,plain,(
    ! [A_6329] :
      ( r1_tarski('#skF_8',k2_zfmisc_1(A_6329,'#skF_7'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_31647,c_40702])).

tff(c_40792,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_40728])).

tff(c_40845,plain,(
    ! [A_6339,C_6340,B_6341,A_6342] :
      ( m1_subset_1(A_6339,k1_zfmisc_1(k2_zfmisc_1(C_6340,B_6341)))
      | ~ r1_tarski(k2_relat_1(A_6339),B_6341)
      | ~ r1_tarski(A_6339,k2_zfmisc_1(C_6340,A_6342)) ) ),
    inference(resolution,[status(thm)],[c_22,c_31667])).

tff(c_40973,plain,(
    ! [B_6349] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_6349)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_6349) ) ),
    inference(resolution,[status(thm)],[c_256,c_40845])).

tff(c_40997,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_40973])).

tff(c_41007,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_40792,c_40997])).

tff(c_41010,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32072,c_41007])).

tff(c_41020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36934,c_41010])).

tff(c_41022,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_40728])).

tff(c_41035,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_41022,c_20])).

tff(c_41046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40199,c_41035])).

tff(c_41047,plain,(
    ! [D_6306] : ~ r2_hidden(D_6306,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_40198])).

tff(c_37014,plain,(
    ! [A_6178,B_6179] :
      ( r2_hidden('#skF_3'(A_6178,B_6179),k1_relat_1(A_6178))
      | r2_hidden('#skF_4'(A_6178,B_6179),B_6179)
      | k2_relat_1(A_6178) = B_6179
      | ~ v1_funct_1(A_6178)
      | ~ v1_relat_1(A_6178) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_37037,plain,(
    ! [B_6179] :
      ( r2_hidden('#skF_3'('#skF_8',B_6179),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_6179),B_6179)
      | k2_relat_1('#skF_8') = B_6179
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_37014])).

tff(c_37050,plain,(
    ! [B_6180] :
      ( r2_hidden('#skF_3'('#skF_8',B_6180),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_6180),B_6180)
      | k2_relat_1('#skF_8') = B_6180 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_37037])).

tff(c_37356,plain,(
    ! [B_6195] :
      ( ~ r1_tarski(B_6195,'#skF_4'('#skF_8',B_6195))
      | r2_hidden('#skF_3'('#skF_8',B_6195),'#skF_6')
      | k2_relat_1('#skF_8') = B_6195 ) ),
    inference(resolution,[status(thm)],[c_37050,c_52])).

tff(c_37372,plain,
    ( r2_hidden('#skF_3'('#skF_8',k2_relat_1(k1_xboole_0)),'#skF_6')
    | k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_806,c_37356])).

tff(c_37374,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_37372])).

tff(c_37383,plain,(
    ! [B_212] : r1_tarski(k2_relat_1('#skF_8'),B_212) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37374,c_806])).

tff(c_37436,plain,(
    ! [C_19,A_16] :
      ( r2_hidden(C_19,A_16)
      | ~ r2_hidden(C_19,k2_relat_1('#skF_8'))
      | ~ v5_relat_1(k1_xboole_0,A_16)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37374,c_30])).

tff(c_37897,plain,(
    ! [C_6212,A_6213] :
      ( r2_hidden(C_6212,A_6213)
      | ~ r2_hidden(C_6212,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_324,c_37436])).

tff(c_37916,plain,(
    ! [D_60,A_6213] :
      ( r2_hidden(k1_funct_1('#skF_8',D_60),A_6213)
      | ~ r2_hidden(D_60,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_37897])).

tff(c_38094,plain,(
    ! [D_6221,A_6222] :
      ( r2_hidden(k1_funct_1('#skF_8',D_6221),A_6222)
      | ~ r2_hidden(D_6221,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_37916])).

tff(c_38123,plain,(
    ! [A_6223,D_6224] :
      ( ~ r1_tarski(A_6223,k1_funct_1('#skF_8',D_6224))
      | ~ r2_hidden(D_6224,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_38094,c_52])).

tff(c_38153,plain,(
    ! [D_6225] : ~ r2_hidden(D_6225,'#skF_6') ),
    inference(resolution,[status(thm)],[c_37383,c_38123])).

tff(c_38191,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_38153])).

tff(c_38200,plain,(
    ! [B_6226] : r1_tarski('#skF_6',B_6226) ),
    inference(resolution,[status(thm)],[c_6,c_38153])).

tff(c_37382,plain,(
    ! [B_213] :
      ( k2_relat_1('#skF_8') = B_213
      | ~ r1_tarski(B_213,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37374,c_37374,c_866])).

tff(c_38249,plain,(
    k2_relat_1('#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_38200,c_37382])).

tff(c_38279,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38249,c_256])).

tff(c_38911,plain,(
    ! [A_6244,C_6245,B_6246,A_6247] :
      ( m1_subset_1(A_6244,k1_zfmisc_1(k2_zfmisc_1(C_6245,B_6246)))
      | ~ r1_tarski(k2_relat_1(A_6244),B_6246)
      | ~ r1_tarski(A_6244,k2_zfmisc_1(C_6245,A_6247)) ) ),
    inference(resolution,[status(thm)],[c_22,c_31667])).

tff(c_38913,plain,(
    ! [B_6246] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_6246)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_6246) ) ),
    inference(resolution,[status(thm)],[c_38279,c_38911])).

tff(c_38944,plain,(
    ! [B_6248] : m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_6248))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38191,c_38249,c_38913])).

tff(c_38955,plain,(
    ! [B_6248] : k1_relset_1('#skF_6',B_6248,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38944,c_58])).

tff(c_38974,plain,(
    ! [B_6248] : k1_relset_1('#skF_6',B_6248,'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_38955])).

tff(c_38979,plain,(
    ! [B_6248] : r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',B_6248)) ),
    inference(resolution,[status(thm)],[c_38944,c_20])).

tff(c_39311,plain,(
    ! [B_6265,A_6266,A_6267] :
      ( k1_xboole_0 = B_6265
      | v1_funct_2(A_6266,A_6267,B_6265)
      | k1_relset_1(A_6267,B_6265,A_6266) != A_6267
      | ~ r1_tarski(A_6266,k2_zfmisc_1(A_6267,B_6265)) ) ),
    inference(resolution,[status(thm)],[c_22,c_32244])).

tff(c_39314,plain,(
    ! [B_6248] :
      ( k1_xboole_0 = B_6248
      | v1_funct_2('#skF_8','#skF_6',B_6248)
      | k1_relset_1('#skF_6',B_6248,'#skF_8') != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_38979,c_39311])).

tff(c_39351,plain,(
    ! [B_6268] :
      ( k1_xboole_0 = B_6268
      | v1_funct_2('#skF_8','#skF_6',B_6268) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38974,c_39314])).

tff(c_39362,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_39351,c_167])).

tff(c_36952,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(resolution,[status(thm)],[c_36934,c_8])).

tff(c_36991,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_36952])).

tff(c_39375,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39362,c_36991])).

tff(c_39418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_39375])).

tff(c_39419,plain,(
    r2_hidden('#skF_3'('#skF_8',k2_relat_1(k1_xboole_0)),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_37372])).

tff(c_41054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41047,c_39419])).

tff(c_41055,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_36952])).

tff(c_41107,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41055,c_119])).

tff(c_41112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32243,c_41107])).

tff(c_41114,plain,(
    v1_relat_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_32242])).

tff(c_41143,plain,(
    ! [A_6355,B_6356] :
      ( r2_hidden('#skF_3'(A_6355,B_6356),k1_relat_1(A_6355))
      | r2_hidden('#skF_4'(A_6355,B_6356),B_6356)
      | k2_relat_1(A_6355) = B_6356
      | ~ v1_funct_1(A_6355)
      | ~ v1_relat_1(A_6355) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_41166,plain,(
    ! [B_6356] :
      ( r2_hidden('#skF_3'('#skF_8',B_6356),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_6356),B_6356)
      | k2_relat_1('#skF_8') = B_6356
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_41143])).

tff(c_41202,plain,(
    ! [B_6358] :
      ( r2_hidden('#skF_3'('#skF_8',B_6358),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_6358),B_6358)
      | k2_relat_1('#skF_8') = B_6358 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_41166])).

tff(c_41257,plain,(
    ! [B_6360] :
      ( ~ r1_tarski(B_6360,'#skF_4'('#skF_8',B_6360))
      | r2_hidden('#skF_3'('#skF_8',B_6360),'#skF_6')
      | k2_relat_1('#skF_8') = B_6360 ) ),
    inference(resolution,[status(thm)],[c_41202,c_52])).

tff(c_41273,plain,
    ( r2_hidden('#skF_3'('#skF_8',k2_relat_1(k1_xboole_0)),'#skF_6')
    | k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_806,c_41257])).

tff(c_41275,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_41273])).

tff(c_41284,plain,(
    ! [B_212] : r1_tarski(k2_relat_1('#skF_8'),B_212) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41275,c_806])).

tff(c_41335,plain,(
    ! [C_19,A_16] :
      ( r2_hidden(C_19,A_16)
      | ~ r2_hidden(C_19,k2_relat_1('#skF_8'))
      | ~ v5_relat_1(k1_xboole_0,A_16)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41275,c_30])).

tff(c_41786,plain,(
    ! [C_6379,A_6380] :
      ( r2_hidden(C_6379,A_6380)
      | ~ r2_hidden(C_6379,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_324,c_41335])).

tff(c_41811,plain,(
    ! [D_60,A_6380] :
      ( r2_hidden(k1_funct_1('#skF_8',D_60),A_6380)
      | ~ r2_hidden(D_60,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_41786])).

tff(c_42086,plain,(
    ! [D_6391,A_6392] :
      ( r2_hidden(k1_funct_1('#skF_8',D_6391),A_6392)
      | ~ r2_hidden(D_6391,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_41811])).

tff(c_42117,plain,(
    ! [A_6393,D_6394] :
      ( ~ r1_tarski(A_6393,k1_funct_1('#skF_8',D_6394))
      | ~ r2_hidden(D_6394,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42086,c_52])).

tff(c_42147,plain,(
    ! [D_6395] : ~ r2_hidden(D_6395,'#skF_6') ),
    inference(resolution,[status(thm)],[c_41284,c_42117])).

tff(c_42185,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_42147])).

tff(c_42194,plain,(
    ! [B_6396] : r1_tarski('#skF_6',B_6396) ),
    inference(resolution,[status(thm)],[c_6,c_42147])).

tff(c_41283,plain,(
    ! [B_213] :
      ( k2_relat_1('#skF_8') = B_213
      | ~ r1_tarski(B_213,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41275,c_41275,c_866])).

tff(c_42243,plain,(
    k2_relat_1('#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42194,c_41283])).

tff(c_42298,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42243,c_256])).

tff(c_43029,plain,(
    ! [A_6421,C_6422,B_6423,A_6424] :
      ( m1_subset_1(A_6421,k1_zfmisc_1(k2_zfmisc_1(C_6422,B_6423)))
      | ~ r1_tarski(k2_relat_1(A_6421),B_6423)
      | ~ r1_tarski(A_6421,k2_zfmisc_1(C_6422,A_6424)) ) ),
    inference(resolution,[status(thm)],[c_22,c_31667])).

tff(c_43031,plain,(
    ! [B_6423] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_6423)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_6423) ) ),
    inference(resolution,[status(thm)],[c_42298,c_43029])).

tff(c_43059,plain,(
    ! [B_6425] : m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_6425))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42185,c_42243,c_43031])).

tff(c_43070,plain,(
    ! [B_6425] : k1_relset_1('#skF_6',B_6425,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_43059,c_58])).

tff(c_43089,plain,(
    ! [B_6425] : k1_relset_1('#skF_6',B_6425,'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_43070])).

tff(c_43094,plain,(
    ! [B_6425] : r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',B_6425)) ),
    inference(resolution,[status(thm)],[c_43059,c_20])).

tff(c_41115,plain,(
    ! [B_6350,C_6351,A_6352] :
      ( k1_xboole_0 = B_6350
      | v1_funct_2(C_6351,A_6352,B_6350)
      | k1_relset_1(A_6352,B_6350,C_6351) != A_6352
      | ~ m1_subset_1(C_6351,k1_zfmisc_1(k2_zfmisc_1(A_6352,B_6350))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_43247,plain,(
    ! [B_6434,A_6435,A_6436] :
      ( k1_xboole_0 = B_6434
      | v1_funct_2(A_6435,A_6436,B_6434)
      | k1_relset_1(A_6436,B_6434,A_6435) != A_6436
      | ~ r1_tarski(A_6435,k2_zfmisc_1(A_6436,B_6434)) ) ),
    inference(resolution,[status(thm)],[c_22,c_41115])).

tff(c_43250,plain,(
    ! [B_6425] :
      ( k1_xboole_0 = B_6425
      | v1_funct_2('#skF_8','#skF_6',B_6425)
      | k1_relset_1('#skF_6',B_6425,'#skF_8') != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_43094,c_43247])).

tff(c_43287,plain,(
    ! [B_6437] :
      ( k1_xboole_0 = B_6437
      | v1_funct_2('#skF_8','#skF_6',B_6437) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43089,c_43250])).

tff(c_43298,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_43287,c_167])).

tff(c_32241,plain,
    ( v5_relat_1(k2_relat_1('#skF_8'),k1_xboole_0)
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_32234])).

tff(c_41131,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_32241])).

tff(c_43308,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43298,c_41131])).

tff(c_43350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_43308])).

tff(c_43352,plain,(
    k2_relat_1(k1_xboole_0) != k2_relat_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_41273])).

tff(c_45323,plain,(
    ! [A_6538,C_6539,B_6540,A_6541] :
      ( m1_subset_1(A_6538,k1_zfmisc_1(k2_zfmisc_1(C_6539,B_6540)))
      | ~ r1_tarski(k2_relat_1(A_6538),B_6540)
      | ~ r1_tarski(A_6538,k2_zfmisc_1(C_6539,A_6541)) ) ),
    inference(resolution,[status(thm)],[c_22,c_31667])).

tff(c_45460,plain,(
    ! [B_6548] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_6548)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_6548) ) ),
    inference(resolution,[status(thm)],[c_256,c_45323])).

tff(c_45471,plain,(
    ! [B_6548] :
      ( k1_relset_1('#skF_6',B_6548,'#skF_8') = k1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_6548) ) ),
    inference(resolution,[status(thm)],[c_45460,c_58])).

tff(c_45559,plain,(
    ! [B_6550] :
      ( k1_relset_1('#skF_6',B_6550,'#skF_8') = '#skF_6'
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_6550) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_45471])).

tff(c_45588,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_31647,c_45559])).

tff(c_45727,plain,(
    ! [B_6556] :
      ( r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',B_6556))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_6556) ) ),
    inference(resolution,[status(thm)],[c_45460,c_20])).

tff(c_45756,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_31647,c_45727])).

tff(c_46103,plain,(
    ! [B_6572,A_6573,A_6574] :
      ( k1_xboole_0 = B_6572
      | v1_funct_2(A_6573,A_6574,B_6572)
      | k1_relset_1(A_6574,B_6572,A_6573) != A_6574
      | ~ r1_tarski(A_6573,k2_zfmisc_1(A_6574,B_6572)) ) ),
    inference(resolution,[status(thm)],[c_22,c_41115])).

tff(c_46112,plain,
    ( k1_xboole_0 = '#skF_7'
    | v1_funct_2('#skF_8','#skF_6','#skF_7')
    | k1_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_45756,c_46103])).

tff(c_46170,plain,
    ( k1_xboole_0 = '#skF_7'
    | v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45588,c_46112])).

tff(c_46171,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_46170])).

tff(c_44189,plain,(
    ! [D_6488,A_6489,B_6490] :
      ( m1_subset_1(D_6488,k1_zfmisc_1(k2_zfmisc_1(A_6489,B_6490)))
      | ~ r1_tarski(k2_relat_1(D_6488),B_6490)
      | ~ m1_subset_1(D_6488,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_31667])).

tff(c_44223,plain,(
    ! [D_6491,A_6492,B_6493] :
      ( r1_tarski(D_6491,k2_zfmisc_1(A_6492,B_6493))
      | ~ r1_tarski(k2_relat_1(D_6491),B_6493)
      | ~ m1_subset_1(D_6491,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_44189,c_20])).

tff(c_44252,plain,(
    ! [A_6492] :
      ( r1_tarski('#skF_8',k2_zfmisc_1(A_6492,'#skF_7'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_31647,c_44223])).

tff(c_44314,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_44252])).

tff(c_45484,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_45460])).

tff(c_45494,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_44314,c_45484])).

tff(c_45503,plain,
    ( ~ v5_relat_1('#skF_8',k1_xboole_0)
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_45494])).

tff(c_45510,plain,(
    ~ v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_45503])).

tff(c_46199,plain,(
    ~ v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46171,c_45510])).

tff(c_46300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31659,c_46199])).

tff(c_46302,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_44252])).

tff(c_271,plain,(
    ! [C_122,B_9] :
      ( v5_relat_1(C_122,B_9)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_264])).

tff(c_46327,plain,(
    ! [B_6575] : v5_relat_1('#skF_8',B_6575) ),
    inference(resolution,[status(thm)],[c_46302,c_271])).

tff(c_850,plain,(
    ! [B_116] :
      ( k2_relat_1(k1_xboole_0) = k2_relat_1(B_116)
      | ~ v5_relat_1(B_116,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_808,c_229])).

tff(c_46342,plain,
    ( k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_46327,c_850])).

tff(c_46371,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_46342])).

tff(c_46373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43352,c_46371])).

tff(c_46375,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_32241])).

tff(c_31205,plain,(
    ! [A_5913,B_5914] :
      ( r1_tarski(k2_relat_1(A_5913),B_5914)
      | ~ v1_relat_1(A_5913)
      | ~ r1_tarski(A_5913,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_286,c_780])).

tff(c_31255,plain,(
    ! [A_5913] :
      ( k2_relat_1(k1_xboole_0) = k2_relat_1(A_5913)
      | ~ v1_relat_1(A_5913)
      | ~ r1_tarski(A_5913,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_31205,c_866])).

tff(c_46378,plain,
    ( k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_46375,c_31255])).

tff(c_46389,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41114,c_46378])).

tff(c_46407,plain,(
    ! [B_212] : r1_tarski(k2_relat_1('#skF_7'),B_212) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46389,c_806])).

tff(c_46602,plain,(
    ! [A_6577,B_6578] :
      ( r2_hidden('#skF_3'(A_6577,B_6578),k1_relat_1(A_6577))
      | r2_hidden('#skF_4'(A_6577,B_6578),B_6578)
      | k2_relat_1(A_6577) = B_6578
      | ~ v1_funct_1(A_6577)
      | ~ v1_relat_1(A_6577) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46625,plain,(
    ! [B_6578] :
      ( r2_hidden('#skF_3'('#skF_8',B_6578),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_6578),B_6578)
      | k2_relat_1('#skF_8') = B_6578
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_46602])).

tff(c_46704,plain,(
    ! [B_6582] :
      ( r2_hidden('#skF_3'('#skF_8',B_6582),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_6582),B_6582)
      | k2_relat_1('#skF_8') = B_6582 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_46625])).

tff(c_47146,plain,(
    ! [B_6606] :
      ( ~ r1_tarski(B_6606,'#skF_4'('#skF_8',B_6606))
      | r2_hidden('#skF_3'('#skF_8',B_6606),'#skF_6')
      | k2_relat_1('#skF_8') = B_6606 ) ),
    inference(resolution,[status(thm)],[c_46704,c_52])).

tff(c_47159,plain,
    ( r2_hidden('#skF_3'('#skF_8',k2_relat_1('#skF_7')),'#skF_6')
    | k2_relat_1('#skF_7') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_46407,c_47146])).

tff(c_47724,plain,(
    k2_relat_1('#skF_7') = k2_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_47159])).

tff(c_47737,plain,(
    ! [B_212] : r1_tarski(k2_relat_1('#skF_8'),B_212) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47724,c_46407])).

tff(c_47976,plain,(
    ! [A_6633,C_6634,B_6635,A_6636] :
      ( m1_subset_1(A_6633,k1_zfmisc_1(k2_zfmisc_1(C_6634,B_6635)))
      | ~ r1_tarski(k2_relat_1(A_6633),B_6635)
      | ~ r1_tarski(A_6633,k2_zfmisc_1(C_6634,A_6636)) ) ),
    inference(resolution,[status(thm)],[c_22,c_31667])).

tff(c_47984,plain,(
    ! [B_6635] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_6635)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_6635) ) ),
    inference(resolution,[status(thm)],[c_256,c_47976])).

tff(c_48926,plain,(
    ! [B_6650] : m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_6650))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47737,c_47984])).

tff(c_48937,plain,(
    ! [B_6650] : k1_relset_1('#skF_6',B_6650,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48926,c_58])).

tff(c_48956,plain,(
    ! [B_6650] : k1_relset_1('#skF_6',B_6650,'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_48937])).

tff(c_48961,plain,(
    ! [B_6650] : r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',B_6650)) ),
    inference(resolution,[status(thm)],[c_48926,c_20])).

tff(c_49199,plain,(
    ! [B_6666,A_6667,A_6668] :
      ( k1_xboole_0 = B_6666
      | v1_funct_2(A_6667,A_6668,B_6666)
      | k1_relset_1(A_6668,B_6666,A_6667) != A_6668
      | ~ r1_tarski(A_6667,k2_zfmisc_1(A_6668,B_6666)) ) ),
    inference(resolution,[status(thm)],[c_22,c_41115])).

tff(c_49202,plain,(
    ! [B_6650] :
      ( k1_xboole_0 = B_6650
      | v1_funct_2('#skF_8','#skF_6',B_6650)
      | k1_relset_1('#skF_6',B_6650,'#skF_8') != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_48961,c_49199])).

tff(c_49252,plain,(
    ! [B_6670] :
      ( k1_xboole_0 = B_6670
      | v1_funct_2('#skF_8','#skF_6',B_6670) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48956,c_49202])).

tff(c_49263,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_49252,c_167])).

tff(c_46395,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(resolution,[status(thm)],[c_46375,c_8])).

tff(c_46792,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_46395])).

tff(c_49277,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49263,c_46792])).

tff(c_49321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_49277])).

tff(c_49323,plain,(
    k2_relat_1('#skF_7') != k2_relat_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_47159])).

tff(c_49335,plain,(
    ! [A_6671,C_6672,B_6673,A_6674] :
      ( m1_subset_1(A_6671,k1_zfmisc_1(k2_zfmisc_1(C_6672,B_6673)))
      | ~ r1_tarski(k2_relat_1(A_6671),B_6673)
      | ~ r1_tarski(A_6671,k2_zfmisc_1(C_6672,A_6674)) ) ),
    inference(resolution,[status(thm)],[c_22,c_31667])).

tff(c_49419,plain,(
    ! [B_6677] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_6677)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_6677) ) ),
    inference(resolution,[status(thm)],[c_256,c_49335])).

tff(c_49443,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_49419])).

tff(c_49488,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_49443])).

tff(c_49491,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32072,c_49488])).

tff(c_49501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46375,c_49491])).

tff(c_49502,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_49443])).

tff(c_49550,plain,(
    ! [B_6680] : v5_relat_1('#skF_8',B_6680) ),
    inference(resolution,[status(thm)],[c_49502,c_271])).

tff(c_46402,plain,(
    ! [B_116] :
      ( k2_relat_1(B_116) = k2_relat_1('#skF_7')
      | ~ v5_relat_1(B_116,k2_relat_1('#skF_7'))
      | ~ v1_relat_1(B_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46389,c_46389,c_850])).

tff(c_49554,plain,
    ( k2_relat_1('#skF_7') = k2_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_49550,c_46402])).

tff(c_49581,plain,(
    k2_relat_1('#skF_7') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_49554])).

tff(c_49583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49323,c_49581])).

tff(c_49584,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_46395])).

tff(c_49627,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49584,c_49584,c_16])).

tff(c_50340,plain,(
    ! [A_6723,C_6724,B_6725,A_6726] :
      ( m1_subset_1(A_6723,k1_zfmisc_1(k2_zfmisc_1(C_6724,B_6725)))
      | ~ r1_tarski(k2_relat_1(A_6723),B_6725)
      | ~ r1_tarski(A_6723,k2_zfmisc_1(C_6724,A_6726)) ) ),
    inference(resolution,[status(thm)],[c_22,c_31667])).

tff(c_50368,plain,(
    ! [B_6727] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_6727)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_6727) ) ),
    inference(resolution,[status(thm)],[c_256,c_50340])).

tff(c_50386,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7'))
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_49627,c_50368])).

tff(c_50395,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31647,c_50386])).

tff(c_49620,plain,(
    ! [C_122,B_9] :
      ( v5_relat_1(C_122,B_9)
      | ~ m1_subset_1(C_122,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49584,c_271])).

tff(c_50411,plain,(
    ! [B_6729] : v5_relat_1('#skF_8',B_6729) ),
    inference(resolution,[status(thm)],[c_50395,c_49620])).

tff(c_50419,plain,(
    ! [B_95] :
      ( r1_tarski(k2_relat_1('#skF_8'),B_95)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_50411,c_228])).

tff(c_50464,plain,(
    ! [B_6730] : r1_tarski(k2_relat_1('#skF_8'),B_6730) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_50419])).

tff(c_31111,plain,(
    ! [A_5902,D_5903] :
      ( ~ r1_tarski(k2_relat_1(A_5902),k1_funct_1(A_5902,D_5903))
      | ~ r2_hidden(D_5903,k1_relat_1(A_5902))
      | ~ v1_funct_1(A_5902)
      | ~ v1_relat_1(A_5902) ) ),
    inference(resolution,[status(thm)],[c_31101,c_52])).

tff(c_50471,plain,(
    ! [D_5903] :
      ( ~ r2_hidden(D_5903,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_50464,c_31111])).

tff(c_50566,plain,(
    ! [D_6732] : ~ r2_hidden(D_6732,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_50471])).

tff(c_50613,plain,(
    ! [B_6733] : r1_tarski('#skF_6',B_6733) ),
    inference(resolution,[status(thm)],[c_6,c_50566])).

tff(c_46406,plain,(
    ! [B_213] :
      ( k2_relat_1('#skF_7') = B_213
      | ~ r1_tarski(B_213,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46389,c_46389,c_866])).

tff(c_50655,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_50613,c_46406])).

tff(c_592,plain,(
    ! [B_185,B_186,A_187] :
      ( v5_relat_1(k2_relat_1(B_185),B_186)
      | ~ v5_relat_1(B_185,k2_zfmisc_1(A_187,B_186))
      | ~ v1_relat_1(B_185) ) ),
    inference(resolution,[status(thm)],[c_26,c_289])).

tff(c_595,plain,(
    ! [B_186] :
      ( v5_relat_1(k2_relat_1(k1_xboole_0),B_186)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_324,c_592])).

tff(c_613,plain,(
    ! [B_188] : v5_relat_1(k2_relat_1(k1_xboole_0),B_188) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_595])).

tff(c_312,plain,(
    ! [B_13,B_131,A_132] :
      ( v5_relat_1(k2_relat_1(B_13),B_131)
      | ~ v5_relat_1(B_13,k2_zfmisc_1(A_132,B_131))
      | ~ v1_relat_1(B_13) ) ),
    inference(resolution,[status(thm)],[c_26,c_289])).

tff(c_621,plain,(
    ! [B_131] :
      ( v5_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)),B_131)
      | ~ v1_relat_1(k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_613,c_312])).

tff(c_673,plain,(
    ~ v1_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_621])).

tff(c_46409,plain,(
    ~ v1_relat_1(k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46389,c_673])).

tff(c_50677,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50655,c_46409])).

tff(c_50604,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_50566])).

tff(c_54954,plain,(
    ! [C_6935,A_6936,B_6937] :
      ( m1_subset_1(k2_zfmisc_1(C_6935,A_6936),k1_zfmisc_1(k2_zfmisc_1(C_6935,B_6937)))
      | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(C_6935,A_6936)),B_6937) ) ),
    inference(resolution,[status(thm)],[c_12,c_50340])).

tff(c_54977,plain,(
    ! [A_8,B_6937] :
      ( m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_8,B_6937)))
      | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(A_8,'#skF_7')),B_6937) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49627,c_54954])).

tff(c_54993,plain,(
    ! [A_6938,B_6939] : m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_6938,B_6939))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50604,c_50655,c_49627,c_54977])).

tff(c_55021,plain,(
    ! [A_6938,B_6939] : r1_tarski('#skF_7',k2_zfmisc_1(A_6938,B_6939)) ),
    inference(resolution,[status(thm)],[c_54993,c_20])).

tff(c_31292,plain,(
    ! [B_5916] :
      ( k2_relat_1(k1_xboole_0) = k2_relat_1(B_5916)
      | ~ v5_relat_1(B_5916,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(B_5916) ) ),
    inference(resolution,[status(thm)],[c_808,c_229])).

tff(c_31316,plain,(
    ! [A_132] :
      ( k2_relat_1(k2_zfmisc_1(A_132,k2_relat_1(k1_xboole_0))) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k2_zfmisc_1(A_132,k2_relat_1(k1_xboole_0))) ) ),
    inference(resolution,[status(thm)],[c_313,c_31292])).

tff(c_31335,plain,(
    ! [A_132] : k2_relat_1(k2_zfmisc_1(A_132,k2_relat_1(k1_xboole_0))) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_31316])).

tff(c_46401,plain,(
    ! [A_132] : k2_relat_1(k2_zfmisc_1(A_132,k2_relat_1('#skF_7'))) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46389,c_46389,c_31335])).

tff(c_50671,plain,(
    ! [A_132] : k2_relat_1(k2_zfmisc_1(A_132,'#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50655,c_50655,c_46401])).

tff(c_50997,plain,(
    ! [A_6742] : k2_relat_1(k2_zfmisc_1(A_6742,'#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50655,c_50655,c_46401])).

tff(c_51037,plain,(
    ! [A_6742] :
      ( r1_tarski(k2_zfmisc_1(A_6742,'#skF_6'),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_6742,'#skF_6')),'#skF_6'))
      | ~ v1_relat_1(k2_zfmisc_1(A_6742,'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50997,c_32])).

tff(c_52685,plain,(
    ! [A_6844] : r1_tarski(k2_zfmisc_1(A_6844,'#skF_6'),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_6844,'#skF_6')),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_51037])).

tff(c_31675,plain,(
    ! [A_10,C_5935,B_5936,A_5937] :
      ( m1_subset_1(A_10,k1_zfmisc_1(k2_zfmisc_1(C_5935,B_5936)))
      | ~ r1_tarski(k2_relat_1(A_10),B_5936)
      | ~ r1_tarski(A_10,k2_zfmisc_1(C_5935,A_5937)) ) ),
    inference(resolution,[status(thm)],[c_22,c_31667])).

tff(c_52693,plain,(
    ! [A_6844,B_5936] :
      ( m1_subset_1(k2_zfmisc_1(A_6844,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_6844,'#skF_6')),B_5936)))
      | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(A_6844,'#skF_6')),B_5936) ) ),
    inference(resolution,[status(thm)],[c_52685,c_31675])).

tff(c_54051,plain,(
    ! [A_6893,B_6894] : m1_subset_1(k2_zfmisc_1(A_6893,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_6893,'#skF_6')),B_6894))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50604,c_50671,c_52693])).

tff(c_54088,plain,(
    ! [A_6895] : m1_subset_1(k2_zfmisc_1(A_6895,'#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_49627,c_54051])).

tff(c_54117,plain,(
    ! [A_6901] : r1_tarski(k2_zfmisc_1(A_6901,'#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_54088,c_20])).

tff(c_54141,plain,(
    ! [A_6901] :
      ( k2_zfmisc_1(A_6901,'#skF_6') = '#skF_7'
      | ~ r1_tarski('#skF_7',k2_zfmisc_1(A_6901,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_54117,c_8])).

tff(c_55098,plain,(
    ! [A_6942] : k2_zfmisc_1(A_6942,'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55021,c_54141])).

tff(c_49624,plain,(
    ! [B_9,A_8] :
      ( B_9 = '#skF_7'
      | A_8 = '#skF_7'
      | k2_zfmisc_1(A_8,B_9) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49584,c_49584,c_49584,c_14])).

tff(c_55199,plain,(
    ! [A_6942] :
      ( '#skF_7' = '#skF_6'
      | A_6942 = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55098,c_49624])).

tff(c_55212,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_55199])).

tff(c_50524,plain,(
    ! [D_5903] : ~ r2_hidden(D_5903,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_50471])).

tff(c_46634,plain,(
    ! [B_6578] :
      ( r2_hidden('#skF_3'('#skF_8',B_6578),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_6578),B_6578)
      | k2_relat_1('#skF_8') = B_6578 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_46625])).

tff(c_50807,plain,(
    ! [B_6737] :
      ( r2_hidden('#skF_4'('#skF_8',B_6737),B_6737)
      | k2_relat_1('#skF_8') = B_6737 ) ),
    inference(negUnitSimplification,[status(thm)],[c_50524,c_46634])).

tff(c_50826,plain,(
    k2_relat_1('#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_50807,c_50524])).

tff(c_31660,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_31647,c_8])).

tff(c_31666,plain,(
    ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_31660])).

tff(c_50840,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50826,c_31666])).

tff(c_55256,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55212,c_50840])).

tff(c_55288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50604,c_55256])).

tff(c_55688,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_55199])).

tff(c_55689,plain,(
    v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_55688,c_41114])).

tff(c_55842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50677,c_55689])).

tff(c_55843,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_31660])).

tff(c_549,plain,(
    ! [A_10,A_169] :
      ( v4_relat_1(k2_relat_1(A_10),A_169)
      | ~ v1_relat_1(A_10)
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_286,c_524])).

tff(c_55887,plain,(
    ! [A_169] :
      ( v4_relat_1('#skF_7',A_169)
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55843,c_549])).

tff(c_55929,plain,(
    ! [A_169] :
      ( v4_relat_1('#skF_7',A_169)
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_55887])).

tff(c_56007,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_55929])).

tff(c_55850,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55843,c_478])).

tff(c_55853,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55843,c_256])).

tff(c_56162,plain,(
    ! [B_10324,C_10325,A_10326] :
      ( k1_xboole_0 = B_10324
      | v1_funct_2(C_10325,A_10326,B_10324)
      | k1_relset_1(A_10326,B_10324,C_10325) != A_10326
      | ~ m1_subset_1(C_10325,k1_zfmisc_1(k2_zfmisc_1(A_10326,B_10324))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_58510,plain,(
    ! [B_10452,A_10453,A_10454] :
      ( k1_xboole_0 = B_10452
      | v1_funct_2(A_10453,A_10454,B_10452)
      | k1_relset_1(A_10454,B_10452,A_10453) != A_10454
      | ~ r1_tarski(A_10453,k2_zfmisc_1(A_10454,B_10452)) ) ),
    inference(resolution,[status(thm)],[c_22,c_56162])).

tff(c_58530,plain,
    ( k1_xboole_0 = '#skF_7'
    | v1_funct_2('#skF_8','#skF_6','#skF_7')
    | k1_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_55853,c_58510])).

tff(c_58564,plain,
    ( k1_xboole_0 = '#skF_7'
    | v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55850,c_58530])).

tff(c_58565,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_58564])).

tff(c_55905,plain,(
    ! [A_12] :
      ( v5_relat_1('#skF_8',A_12)
      | ~ r1_tarski('#skF_7',A_12)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55843,c_24])).

tff(c_56015,plain,(
    ! [A_10312] :
      ( v5_relat_1('#skF_8',A_10312)
      | ~ r1_tarski('#skF_7',A_10312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_55905])).

tff(c_55890,plain,(
    ! [A_8] :
      ( v4_relat_1('#skF_7',A_8)
      | ~ v5_relat_1('#skF_8',k1_xboole_0)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55843,c_542])).

tff(c_55931,plain,(
    ! [A_8] :
      ( v4_relat_1('#skF_7',A_8)
      | ~ v5_relat_1('#skF_8',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_55890])).

tff(c_56009,plain,(
    ~ v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_55931])).

tff(c_56046,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_56015,c_56009])).

tff(c_58624,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58565,c_56046])).

tff(c_58670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_58624])).

tff(c_58672,plain,(
    v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_55931])).

tff(c_55899,plain,(
    ! [A_12] :
      ( r1_tarski('#skF_7',A_12)
      | ~ v5_relat_1('#skF_8',A_12)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55843,c_26])).

tff(c_55937,plain,(
    ! [A_12] :
      ( r1_tarski('#skF_7',A_12)
      | ~ v5_relat_1('#skF_8',A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_55899])).

tff(c_58679,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_58672,c_55937])).

tff(c_55944,plain,(
    ! [D_10304,C_10305,B_10306,A_10307] :
      ( m1_subset_1(D_10304,k1_zfmisc_1(k2_zfmisc_1(C_10305,B_10306)))
      | ~ r1_tarski(k2_relat_1(D_10304),B_10306)
      | ~ m1_subset_1(D_10304,k1_zfmisc_1(k2_zfmisc_1(C_10305,A_10307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_60574,plain,(
    ! [A_10563,C_10564,B_10565,A_10566] :
      ( m1_subset_1(A_10563,k1_zfmisc_1(k2_zfmisc_1(C_10564,B_10565)))
      | ~ r1_tarski(k2_relat_1(A_10563),B_10565)
      | ~ r1_tarski(A_10563,k2_zfmisc_1(C_10564,A_10566)) ) ),
    inference(resolution,[status(thm)],[c_22,c_55944])).

tff(c_60579,plain,(
    ! [B_10565] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_10565)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_10565) ) ),
    inference(resolution,[status(thm)],[c_55853,c_60574])).

tff(c_60607,plain,(
    ! [B_10567] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_10567)))
      | ~ r1_tarski('#skF_7',B_10567) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55843,c_60579])).

tff(c_60631,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_60607])).

tff(c_60643,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58679,c_60631])).

tff(c_60656,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_60643,c_20])).

tff(c_60667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56007,c_60656])).

tff(c_60669,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_55929])).

tff(c_60674,plain,
    ( k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60669,c_31255])).

tff(c_60685,plain,(
    k2_relat_1(k1_xboole_0) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_55843,c_60674])).

tff(c_412,plain,(
    ! [B_153,D_154] :
      ( ~ r1_tarski(B_153,k1_funct_1('#skF_8',D_154))
      | ~ r1_tarski('#skF_7',B_153)
      | ~ r2_hidden(D_154,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_330,c_52])).

tff(c_735,plain,(
    ! [B_207,D_208] :
      ( ~ r1_tarski('#skF_7',k2_relat_1(B_207))
      | ~ r2_hidden(D_208,'#skF_6')
      | ~ v5_relat_1(B_207,k1_funct_1('#skF_8',D_208))
      | ~ v1_relat_1(B_207) ) ),
    inference(resolution,[status(thm)],[c_26,c_412])).

tff(c_755,plain,(
    ! [D_208] :
      ( ~ r1_tarski('#skF_7',k2_relat_1(k1_xboole_0))
      | ~ r2_hidden(D_208,'#skF_6')
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_324,c_735])).

tff(c_770,plain,(
    ! [D_208] :
      ( ~ r1_tarski('#skF_7',k2_relat_1(k1_xboole_0))
      | ~ r2_hidden(D_208,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_755])).

tff(c_775,plain,(
    ~ r1_tarski('#skF_7',k2_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_770])).

tff(c_60701,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60685,c_775])).

tff(c_60707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_60701])).

tff(c_60709,plain,(
    r1_tarski('#skF_7',k2_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_770])).

tff(c_60786,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_7'
    | ~ v5_relat_1(k1_xboole_0,'#skF_7')
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_60709,c_229])).

tff(c_60791,plain,(
    k2_relat_1(k1_xboole_0) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_324,c_60786])).

tff(c_60824,plain,(
    ! [A_12] :
      ( r1_tarski('#skF_7',A_12)
      | ~ v5_relat_1(k1_xboole_0,A_12)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60791,c_26])).

tff(c_60850,plain,(
    ! [A_12] : r1_tarski('#skF_7',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_324,c_60824])).

tff(c_60710,plain,(
    ! [D_10569] : ~ r2_hidden(D_10569,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_770])).

tff(c_60721,plain,(
    ! [B_10570] : r1_tarski('#skF_6',B_10570) ),
    inference(resolution,[status(thm)],[c_6,c_60710])).

tff(c_60934,plain,(
    ! [B_10580] :
      ( B_10580 = '#skF_6'
      | ~ r1_tarski(B_10580,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_60721,c_8])).

tff(c_60951,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_60850,c_60934])).

tff(c_60794,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60791,c_673])).

tff(c_60960,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60951,c_60794])).

tff(c_60720,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_60710])).

tff(c_60708,plain,(
    ! [D_208] : ~ r2_hidden(D_208,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_770])).

tff(c_61123,plain,(
    ! [A_10591,C_10592] :
      ( r2_hidden('#skF_5'(A_10591,k2_relat_1(A_10591),C_10592),k1_relat_1(A_10591))
      | ~ r2_hidden(C_10592,k2_relat_1(A_10591))
      | ~ v1_funct_1(A_10591)
      | ~ v1_relat_1(A_10591) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_61134,plain,(
    ! [C_10592] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_10592),'#skF_6')
      | ~ r2_hidden(C_10592,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_61123])).

tff(c_61140,plain,(
    ! [C_10592] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_10592),'#skF_6')
      | ~ r2_hidden(C_10592,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_61134])).

tff(c_61142,plain,(
    ! [C_10593] : ~ r2_hidden(C_10593,k2_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_60708,c_61140])).

tff(c_61160,plain,(
    ! [B_10594] : r1_tarski(k2_relat_1('#skF_8'),B_10594) ),
    inference(resolution,[status(thm)],[c_6,c_61142])).

tff(c_60763,plain,(
    ! [B_10570] :
      ( B_10570 = '#skF_6'
      | ~ r1_tarski(B_10570,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_60721,c_8])).

tff(c_61205,plain,(
    k2_relat_1('#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_61160,c_60763])).

tff(c_61106,plain,(
    ! [D_10587,C_10588,B_10589,A_10590] :
      ( m1_subset_1(D_10587,k1_zfmisc_1(k2_zfmisc_1(C_10588,B_10589)))
      | ~ r1_tarski(k2_relat_1(D_10587),B_10589)
      | ~ m1_subset_1(D_10587,k1_zfmisc_1(k2_zfmisc_1(C_10588,A_10590))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_62950,plain,(
    ! [D_10689,A_10690,B_10691] :
      ( m1_subset_1(D_10689,k1_zfmisc_1(k2_zfmisc_1(A_10690,B_10691)))
      | ~ r1_tarski(k2_relat_1(D_10689),B_10691)
      | ~ m1_subset_1(D_10689,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_61106])).

tff(c_62984,plain,(
    ! [D_10692,A_10693,B_10694] :
      ( r1_tarski(D_10692,k2_zfmisc_1(A_10693,B_10694))
      | ~ r1_tarski(k2_relat_1(D_10692),B_10694)
      | ~ m1_subset_1(D_10692,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_62950,c_20])).

tff(c_62992,plain,(
    ! [A_10693,B_10694] :
      ( r1_tarski('#skF_8',k2_zfmisc_1(A_10693,B_10694))
      | ~ r1_tarski('#skF_6',B_10694)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61205,c_62984])).

tff(c_63008,plain,(
    ! [A_10693,B_10694] :
      ( r1_tarski('#skF_8',k2_zfmisc_1(A_10693,B_10694))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60720,c_62992])).

tff(c_63065,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_63008])).

tff(c_61240,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61205,c_256])).

tff(c_64424,plain,(
    ! [A_10748,C_10749,B_10750,A_10751] :
      ( m1_subset_1(A_10748,k1_zfmisc_1(k2_zfmisc_1(C_10749,B_10750)))
      | ~ r1_tarski(k2_relat_1(A_10748),B_10750)
      | ~ r1_tarski(A_10748,k2_zfmisc_1(C_10749,A_10751)) ) ),
    inference(resolution,[status(thm)],[c_22,c_61106])).

tff(c_64453,plain,(
    ! [B_10750] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_10750)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_10750) ) ),
    inference(resolution,[status(thm)],[c_61240,c_64424])).

tff(c_64491,plain,(
    ! [B_10752] : m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_10752))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60720,c_61205,c_64453])).

tff(c_64514,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_64491])).

tff(c_64528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63065,c_64514])).

tff(c_64575,plain,(
    ! [A_10754,B_10755] : r1_tarski('#skF_8',k2_zfmisc_1(A_10754,B_10755)) ),
    inference(splitRight,[status(thm)],[c_63008])).

tff(c_64578,plain,(
    ! [A_10754,B_10755] : k1_relset_1(A_10754,B_10755,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64575,c_386])).

tff(c_64592,plain,(
    ! [A_10754,B_10755] : k1_relset_1(A_10754,B_10755,'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_64578])).

tff(c_64530,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_63008])).

tff(c_64544,plain,(
    ! [B_74] :
      ( v1_funct_2('#skF_8',k1_xboole_0,B_74)
      | k1_relset_1(k1_xboole_0,B_74,'#skF_8') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_64530,c_85])).

tff(c_64686,plain,(
    ! [B_74] :
      ( v1_funct_2('#skF_8',k1_xboole_0,B_74)
      | k1_xboole_0 != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64592,c_64544])).

tff(c_64687,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_64686])).

tff(c_64529,plain,(
    ! [A_10693,B_10694] : r1_tarski('#skF_8',k2_zfmisc_1(A_10693,B_10694)) ),
    inference(splitRight,[status(thm)],[c_63008])).

tff(c_64708,plain,(
    ! [A_10766,C_10767,B_10768,A_10769] :
      ( m1_subset_1(A_10766,k1_zfmisc_1(k2_zfmisc_1(C_10767,B_10768)))
      | ~ r1_tarski(k2_relat_1(A_10766),B_10768)
      | ~ r1_tarski(A_10766,k2_zfmisc_1(C_10767,A_10769)) ) ),
    inference(resolution,[status(thm)],[c_22,c_61106])).

tff(c_64710,plain,(
    ! [A_10693,B_10768] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_10693,B_10768)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_10768) ) ),
    inference(resolution,[status(thm)],[c_64529,c_64708])).

tff(c_64756,plain,(
    ! [A_10770,B_10771] : m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_10770,B_10771))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60720,c_61205,c_64710])).

tff(c_64762,plain,(
    ! [B_10771,A_10770] :
      ( k1_xboole_0 = B_10771
      | v1_funct_2('#skF_8',A_10770,B_10771)
      | k1_relset_1(A_10770,B_10771,'#skF_8') != A_10770 ) ),
    inference(resolution,[status(thm)],[c_64756,c_68])).

tff(c_64884,plain,(
    ! [B_10779,A_10780] :
      ( k1_xboole_0 = B_10779
      | v1_funct_2('#skF_8',A_10780,B_10779)
      | A_10780 != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64592,c_64762])).

tff(c_60962,plain,(
    ~ v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60951,c_167])).

tff(c_64890,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_64884,c_60962])).

tff(c_64901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64687,c_64890])).

tff(c_64903,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_64686])).

tff(c_64552,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_64530,c_20])).

tff(c_64573,plain,
    ( k1_xboole_0 = '#skF_8'
    | ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(resolution,[status(thm)],[c_64552,c_8])).

tff(c_64682,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_64573])).

tff(c_64904,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64903,c_64682])).

tff(c_64955,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60720,c_64904])).

tff(c_64956,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_64573])).

tff(c_60961,plain,(
    k2_relat_1(k1_xboole_0) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60951,c_60791])).

tff(c_60973,plain,(
    ! [D_60] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_60),'#skF_6')
      | ~ r2_hidden(D_60,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60961,c_34])).

tff(c_61009,plain,(
    ! [D_60] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_60),'#skF_6')
      | ~ r2_hidden(D_60,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_60973])).

tff(c_61010,plain,(
    ! [D_60] :
      ( ~ r2_hidden(D_60,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60708,c_61009])).

tff(c_61360,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_61010])).

tff(c_64980,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64956,c_61360])).

tff(c_65013,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_64980])).

tff(c_65016,plain,(
    ! [D_10781] : ~ r2_hidden(D_10781,k1_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_61010])).

tff(c_65047,plain,(
    ! [B_10785] : r1_tarski(k1_relat_1(k1_xboole_0),B_10785) ),
    inference(resolution,[status(thm)],[c_6,c_65016])).

tff(c_65089,plain,(
    k1_relat_1(k1_xboole_0) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_65047,c_60763])).

tff(c_60774,plain,(
    ! [C_10572,B_10573] :
      ( v1_funct_2(C_10572,k1_xboole_0,B_10573)
      | k1_relset_1(k1_xboole_0,B_10573,C_10572) != k1_xboole_0
      | ~ m1_subset_1(C_10572,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_66])).

tff(c_60776,plain,(
    ! [B_10573] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_10573)
      | k1_relset_1(k1_xboole_0,B_10573,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_347,c_60774])).

tff(c_60781,plain,(
    ! [B_10573] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_10573)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_60776])).

tff(c_65182,plain,(
    ! [B_10573] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_10573)
      | k1_xboole_0 != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65089,c_60781])).

tff(c_65183,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_65182])).

tff(c_67674,plain,(
    ! [A_10907,C_10908,B_10909,A_10910] :
      ( m1_subset_1(A_10907,k1_zfmisc_1(k2_zfmisc_1(C_10908,B_10909)))
      | ~ r1_tarski(k2_relat_1(A_10907),B_10909)
      | ~ r1_tarski(A_10907,k2_zfmisc_1(C_10908,A_10910)) ) ),
    inference(resolution,[status(thm)],[c_22,c_61106])).

tff(c_67695,plain,(
    ! [B_10909] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_10909)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_10909) ) ),
    inference(resolution,[status(thm)],[c_61240,c_67674])).

tff(c_67730,plain,(
    ! [B_10911] : m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_10911))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60720,c_61205,c_67695])).

tff(c_67741,plain,(
    ! [B_10911] : k1_relset_1('#skF_6',B_10911,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_67730,c_58])).

tff(c_67760,plain,(
    ! [B_10911] : k1_relset_1('#skF_6',B_10911,'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_67741])).

tff(c_67765,plain,(
    ! [B_10911] : r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',B_10911)) ),
    inference(resolution,[status(thm)],[c_67730,c_20])).

tff(c_61321,plain,(
    ! [B_10596,C_10597,A_10598] :
      ( k1_xboole_0 = B_10596
      | v1_funct_2(C_10597,A_10598,B_10596)
      | k1_relset_1(A_10598,B_10596,C_10597) != A_10598
      | ~ m1_subset_1(C_10597,k1_zfmisc_1(k2_zfmisc_1(A_10598,B_10596))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_68340,plain,(
    ! [B_10936,A_10937,A_10938] :
      ( k1_xboole_0 = B_10936
      | v1_funct_2(A_10937,A_10938,B_10936)
      | k1_relset_1(A_10938,B_10936,A_10937) != A_10938
      | ~ r1_tarski(A_10937,k2_zfmisc_1(A_10938,B_10936)) ) ),
    inference(resolution,[status(thm)],[c_22,c_61321])).

tff(c_68346,plain,(
    ! [B_10911] :
      ( k1_xboole_0 = B_10911
      | v1_funct_2('#skF_8','#skF_6',B_10911)
      | k1_relset_1('#skF_6',B_10911,'#skF_8') != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_67765,c_68340])).

tff(c_68412,plain,(
    ! [B_10939] :
      ( k1_xboole_0 = B_10939
      | v1_funct_2('#skF_8','#skF_6',B_10939) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67760,c_68346])).

tff(c_68415,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_68412,c_60962])).

tff(c_68422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65183,c_68415])).

tff(c_68424,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_65182])).

tff(c_68454,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68424,c_119])).

tff(c_68461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60960,c_68454])).

tff(c_68463,plain,(
    v1_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_621])).

tff(c_608,plain,(
    ! [B_186] : v5_relat_1(k2_relat_1(k1_xboole_0),B_186) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_595])).

tff(c_91518,plain,(
    ! [B_12013] :
      ( r1_tarski(k2_relat_1(k2_relat_1(k1_xboole_0)),B_12013)
      | ~ v1_relat_1(k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_608,c_91498])).

tff(c_91535,plain,(
    ! [B_12013] : r1_tarski(k2_relat_1(k2_relat_1(k1_xboole_0)),B_12013) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68463,c_91518])).

tff(c_91765,plain,(
    ! [B_12019] :
      ( k2_relat_1(k1_xboole_0) = B_12019
      | ~ r1_tarski(B_12019,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_91540,c_8])).

tff(c_91787,plain,(
    k2_relat_1(k2_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_91535,c_91765])).

tff(c_91829,plain,(
    ! [C_19,A_16] :
      ( r2_hidden(C_19,A_16)
      | ~ r2_hidden(C_19,k2_relat_1(k1_xboole_0))
      | ~ v5_relat_1(k2_relat_1(k1_xboole_0),A_16)
      | ~ v1_relat_1(k2_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91787,c_30])).

tff(c_91898,plain,(
    ! [C_12023,A_12024] :
      ( r2_hidden(C_12023,A_12024)
      | ~ r2_hidden(C_12023,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68463,c_608,c_91829])).

tff(c_91901,plain,(
    ! [D_60,A_12024] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_60),A_12024)
      | ~ r2_hidden(D_60,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_91898])).

tff(c_91913,plain,(
    ! [D_60,A_12024] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_60),A_12024)
      | ~ r2_hidden(D_60,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_91387,c_91901])).

tff(c_92398,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_91913])).

tff(c_99802,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99786,c_92398])).

tff(c_99836,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_99802])).

tff(c_99837,plain,(
    r2_hidden('#skF_3'('#skF_8',k2_relat_1(k1_xboole_0)),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_92769])).

tff(c_102338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102332,c_99837])).

tff(c_102342,plain,(
    ! [D_15465,A_15466] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_15465),A_15466)
      | ~ r2_hidden(D_15465,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_91913])).

tff(c_102369,plain,(
    ! [A_15467,D_15468] :
      ( ~ r1_tarski(A_15467,k1_funct_1(k1_xboole_0,D_15468))
      | ~ r2_hidden(D_15468,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_102342,c_52])).

tff(c_102393,plain,(
    ! [D_15469] : ~ r2_hidden(D_15469,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_91538,c_102369])).

tff(c_102408,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_102393])).

tff(c_102390,plain,(
    ! [D_15468] : ~ r2_hidden(D_15468,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_91538,c_102369])).

tff(c_102340,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_91913])).

tff(c_102422,plain,(
    ! [B_15473] : r1_tarski(k1_xboole_0,B_15473) ),
    inference(resolution,[status(thm)],[c_6,c_102393])).

tff(c_102478,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_102422,c_91598])).

tff(c_102742,plain,(
    ! [A_15484,B_15485] :
      ( r2_hidden('#skF_3'(A_15484,B_15485),k1_relat_1(A_15484))
      | r2_hidden('#skF_4'(A_15484,B_15485),B_15485)
      | k2_relat_1(A_15484) = B_15485
      | ~ v1_funct_1(A_15484)
      | ~ v1_relat_1(A_15484) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_102762,plain,(
    ! [B_15485] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_15485),k1_xboole_0)
      | r2_hidden('#skF_4'(k1_xboole_0,B_15485),B_15485)
      | k2_relat_1(k1_xboole_0) = B_15485
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91387,c_102742])).

tff(c_102772,plain,(
    ! [B_15485] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_15485),k1_xboole_0)
      | r2_hidden('#skF_4'(k1_xboole_0,B_15485),B_15485)
      | k1_xboole_0 = B_15485 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_102340,c_102478,c_102762])).

tff(c_102776,plain,(
    ! [B_15486] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_15486),B_15486)
      | k1_xboole_0 = B_15486 ) ),
    inference(negUnitSimplification,[status(thm)],[c_102390,c_102772])).

tff(c_92288,plain,(
    ! [C_12042] :
      ( r2_hidden(C_12042,'#skF_7')
      | ~ r2_hidden(C_12042,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_92279,c_91645])).

tff(c_102795,plain,
    ( r2_hidden('#skF_4'(k1_xboole_0,k2_relat_1('#skF_8')),'#skF_7')
    | k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_102776,c_92288])).

tff(c_103003,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_102795])).

tff(c_103014,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_6',k1_xboole_0),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103003,c_287])).

tff(c_103021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102408,c_16,c_103014])).

tff(c_103023,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_102795])).

tff(c_102765,plain,(
    ! [B_15485] :
      ( r2_hidden('#skF_3'('#skF_8',B_15485),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_15485),B_15485)
      | k2_relat_1('#skF_8') = B_15485
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_102742])).

tff(c_102816,plain,(
    ! [B_15488] :
      ( r2_hidden('#skF_3'('#skF_8',B_15488),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_15488),B_15488)
      | k2_relat_1('#skF_8') = B_15488 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_102765])).

tff(c_103256,plain,(
    ! [B_15518] :
      ( ~ r1_tarski(B_15518,'#skF_4'('#skF_8',B_15518))
      | r2_hidden('#skF_3'('#skF_8',B_15518),'#skF_6')
      | k2_relat_1('#skF_8') = B_15518 ) ),
    inference(resolution,[status(thm)],[c_102816,c_52])).

tff(c_103262,plain,
    ( r2_hidden('#skF_3'('#skF_8',k1_xboole_0),'#skF_6')
    | k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_102408,c_103256])).

tff(c_103272,plain,(
    r2_hidden('#skF_3'('#skF_8',k1_xboole_0),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_103023,c_103262])).

tff(c_105327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105321,c_103272])).

tff(c_105328,plain,(
    k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_137096,plain,(
    k2_zfmisc_1('#skF_6','#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137059,c_105328])).

tff(c_137003,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_136965])).

tff(c_105395,plain,(
    ! [A_15613,B_15612] : v5_relat_1(k2_zfmisc_1(A_15613,B_15612),B_15612) ),
    inference(resolution,[status(thm)],[c_12,c_105372])).

tff(c_117688,plain,(
    ! [B_20996] :
      ( k2_relat_1(k1_xboole_0) = k2_relat_1(B_20996)
      | ~ v5_relat_1(B_20996,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(B_20996) ) ),
    inference(resolution,[status(thm)],[c_117452,c_229])).

tff(c_117712,plain,(
    ! [A_15613] :
      ( k2_relat_1(k2_zfmisc_1(A_15613,k2_relat_1(k1_xboole_0))) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k2_zfmisc_1(A_15613,k2_relat_1(k1_xboole_0))) ) ),
    inference(resolution,[status(thm)],[c_105395,c_117688])).

tff(c_117731,plain,(
    ! [A_15613] : k2_relat_1(k2_zfmisc_1(A_15613,k2_relat_1(k1_xboole_0))) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_117712])).

tff(c_136167,plain,(
    ! [A_15613] : k2_relat_1(k2_zfmisc_1(A_15613,k2_relat_1('#skF_8'))) = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136164,c_136164,c_117731])).

tff(c_137076,plain,(
    ! [A_15613] : k2_relat_1(k2_zfmisc_1(A_15613,'#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137059,c_137059,c_136167])).

tff(c_137582,plain,(
    ! [A_21810] : k2_relat_1(k2_zfmisc_1(A_21810,'#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137059,c_137059,c_136167])).

tff(c_137660,plain,(
    ! [A_21810] :
      ( r1_tarski(k2_zfmisc_1(A_21810,'#skF_6'),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21810,'#skF_6')),'#skF_6'))
      | ~ v1_relat_1(k2_zfmisc_1(A_21810,'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137582,c_32])).

tff(c_138947,plain,(
    ! [A_21883] : r1_tarski(k2_zfmisc_1(A_21883,'#skF_6'),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21883,'#skF_6')),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_137660])).

tff(c_118055,plain,(
    ! [A_10,C_21009,B_21010,A_21011] :
      ( m1_subset_1(A_10,k1_zfmisc_1(k2_zfmisc_1(C_21009,B_21010)))
      | ~ r1_tarski(k2_relat_1(A_10),B_21010)
      | ~ r1_tarski(A_10,k2_zfmisc_1(C_21009,A_21011)) ) ),
    inference(resolution,[status(thm)],[c_22,c_118045])).

tff(c_138955,plain,(
    ! [A_21883,B_21010] :
      ( m1_subset_1(k2_zfmisc_1(A_21883,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21883,'#skF_6')),B_21010)))
      | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(A_21883,'#skF_6')),B_21010) ) ),
    inference(resolution,[status(thm)],[c_138947,c_118055])).

tff(c_140732,plain,(
    ! [A_21939,B_21940] : m1_subset_1(k2_zfmisc_1(A_21939,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21939,'#skF_6')),B_21940))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137003,c_137076,c_138955])).

tff(c_140755,plain,(
    ! [B_21940] : m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1('#skF_6','#skF_6')),B_21940))) ),
    inference(superposition,[status(thm),theory(equality)],[c_137096,c_140732])).

tff(c_140953,plain,(
    ! [B_21950] : m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_21950))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_137096,c_140755])).

tff(c_140964,plain,(
    ! [B_21950] : k1_relset_1('#skF_6',B_21950,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_140953,c_58])).

tff(c_140985,plain,(
    ! [B_21950] : k1_relset_1('#skF_6',B_21950,'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_140964])).

tff(c_141148,plain,(
    ! [B_21955] : r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',B_21955)) ),
    inference(resolution,[status(thm)],[c_140953,c_20])).

tff(c_141154,plain,(
    ! [B_21955] :
      ( k1_xboole_0 = B_21955
      | v1_funct_2('#skF_8','#skF_6',B_21955)
      | k1_relset_1('#skF_6',B_21955,'#skF_8') != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_141148,c_118224])).

tff(c_141193,plain,(
    ! [B_21956] :
      ( k1_xboole_0 = B_21956
      | v1_funct_2('#skF_8','#skF_6',B_21956) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140985,c_141154])).

tff(c_141205,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_141193,c_167])).

tff(c_118483,plain,(
    ! [B_21050,B_21051] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_8'),B_21050),B_21051)
      | ~ r1_tarski('#skF_7',B_21051)
      | r1_tarski(k2_relat_1('#skF_8'),B_21050) ) ),
    inference(resolution,[status(thm)],[c_118014,c_2])).

tff(c_118520,plain,(
    ! [B_21054] :
      ( ~ r1_tarski('#skF_7',B_21054)
      | r1_tarski(k2_relat_1('#skF_8'),B_21054) ) ),
    inference(resolution,[status(thm)],[c_118483,c_4])).

tff(c_118658,plain,(
    ! [B_21056,A_21057] :
      ( v5_relat_1(k2_relat_1('#skF_8'),B_21056)
      | ~ r1_tarski('#skF_7',k2_zfmisc_1(A_21057,B_21056)) ) ),
    inference(resolution,[status(thm)],[c_118520,c_275])).

tff(c_118665,plain,(
    ! [B_9] :
      ( v5_relat_1(k2_relat_1('#skF_8'),B_9)
      | ~ r1_tarski('#skF_7',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_118658])).

tff(c_135901,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_118665])).

tff(c_141230,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141205,c_135901])).

tff(c_141271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_141230])).

tff(c_141272,plain,(
    r2_hidden('#skF_3'('#skF_8',k2_relat_1(k1_xboole_0)),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_136108])).

tff(c_144048,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144041,c_141272])).

tff(c_144050,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_118665])).

tff(c_118508,plain,(
    ! [B_21051] :
      ( ~ r1_tarski('#skF_7',B_21051)
      | r1_tarski(k2_relat_1('#skF_8'),B_21051) ) ),
    inference(resolution,[status(thm)],[c_118483,c_4])).

tff(c_145095,plain,(
    ! [D_22115,A_22116,B_22117] :
      ( m1_subset_1(D_22115,k1_zfmisc_1(k2_zfmisc_1(A_22116,B_22117)))
      | ~ r1_tarski(k2_relat_1(D_22115),B_22117)
      | ~ m1_subset_1(D_22115,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_118045])).

tff(c_152051,plain,(
    ! [D_22374,A_22375,B_22376] :
      ( r1_tarski(D_22374,k2_zfmisc_1(A_22375,B_22376))
      | ~ r1_tarski(k2_relat_1(D_22374),B_22376)
      | ~ m1_subset_1(D_22374,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_145095,c_20])).

tff(c_152090,plain,(
    ! [A_22375] :
      ( r1_tarski('#skF_8',k2_zfmisc_1(A_22375,'#skF_7'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_118025,c_152051])).

tff(c_152387,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_152090])).

tff(c_150455,plain,(
    ! [A_22304,C_22305,B_22306,A_22307] :
      ( m1_subset_1(A_22304,k1_zfmisc_1(k2_zfmisc_1(C_22305,B_22306)))
      | ~ r1_tarski(k2_relat_1(A_22304),B_22306)
      | ~ r1_tarski(A_22304,k2_zfmisc_1(C_22305,A_22307)) ) ),
    inference(resolution,[status(thm)],[c_22,c_118045])).

tff(c_154748,plain,(
    ! [A_22497,B_22498] :
      ( m1_subset_1(A_22497,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_22497),B_22498)))
      | ~ r1_tarski(k2_relat_1(A_22497),B_22498)
      | ~ v1_relat_1(A_22497) ) ),
    inference(resolution,[status(thm)],[c_32,c_150455])).

tff(c_154778,plain,(
    ! [B_22498] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_22498)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_22498)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_154748])).

tff(c_154907,plain,(
    ! [B_22501] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_22501)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_22501) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_154778])).

tff(c_154934,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_154907])).

tff(c_154946,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_152387,c_154934])).

tff(c_154970,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_118508,c_154946])).

tff(c_154980,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144050,c_154970])).

tff(c_154982,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_152090])).

tff(c_154995,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_154982,c_20])).

tff(c_155006,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150873,c_154995])).

tff(c_155007,plain,(
    ! [D_22320] : ~ r2_hidden(D_22320,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_150872])).

tff(c_105347,plain,
    ( k2_relat_1('#skF_8') = k1_xboole_0
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 != '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_105328,c_14])).

tff(c_105358,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_105347])).

tff(c_144071,plain,(
    ! [A_22076,B_22077] :
      ( r2_hidden('#skF_3'(A_22076,B_22077),k1_relat_1(A_22076))
      | r2_hidden('#skF_4'(A_22076,B_22077),B_22077)
      | k2_relat_1(A_22076) = B_22077
      | ~ v1_funct_1(A_22076)
      | ~ v1_relat_1(A_22076) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_144095,plain,(
    ! [B_22077] :
      ( r2_hidden('#skF_3'('#skF_8',B_22077),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_22077),B_22077)
      | k2_relat_1('#skF_8') = B_22077
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_144071])).

tff(c_144104,plain,(
    ! [B_22077] :
      ( r2_hidden('#skF_3'('#skF_8',B_22077),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_22077),B_22077)
      | k2_relat_1('#skF_8') = B_22077 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_144095])).

tff(c_118668,plain,
    ( v5_relat_1(k2_relat_1('#skF_8'),k2_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_118658])).

tff(c_118669,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_118668])).

tff(c_133195,plain,(
    ! [A_21626,D_21627] :
      ( ~ r1_tarski(k2_relat_1(A_21626),k1_funct_1(A_21626,D_21627))
      | ~ r2_hidden(D_21627,k1_relat_1(A_21626))
      | ~ v1_funct_1(A_21626)
      | ~ v1_relat_1(A_21626) ) ),
    inference(resolution,[status(thm)],[c_117387,c_52])).

tff(c_133231,plain,(
    ! [D_21628,A_21629] :
      ( ~ r2_hidden(D_21628,k1_relat_1(A_21629))
      | ~ v1_funct_1(A_21629)
      | ~ v1_relat_1(A_21629)
      | ~ r1_tarski(A_21629,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_117451,c_133195])).

tff(c_133287,plain,(
    ! [D_21628] :
      ( ~ r2_hidden(D_21628,'#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_133231])).

tff(c_133304,plain,(
    ! [D_21628] :
      ( ~ r2_hidden(D_21628,'#skF_6')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_133287])).

tff(c_133305,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_133304])).

tff(c_133553,plain,(
    ! [D_21636,A_21637,B_21638] :
      ( m1_subset_1(D_21636,k1_zfmisc_1(k2_zfmisc_1(A_21637,B_21638)))
      | ~ r1_tarski(k2_relat_1(D_21636),B_21638)
      | ~ m1_subset_1(D_21636,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_118045])).

tff(c_134318,plain,(
    ! [D_21672,A_21673,B_21674] :
      ( r1_tarski(D_21672,k2_zfmisc_1(A_21673,B_21674))
      | ~ r1_tarski(k2_relat_1(D_21672),B_21674)
      | ~ m1_subset_1(D_21672,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_133553,c_20])).

tff(c_134350,plain,(
    ! [A_21673] :
      ( r1_tarski('#skF_8',k2_zfmisc_1(A_21673,'#skF_7'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_118025,c_134318])).

tff(c_134689,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_134350])).

tff(c_124867,plain,(
    ! [A_21303,D_21304] :
      ( ~ r1_tarski(k2_relat_1(A_21303),k1_funct_1(A_21303,D_21304))
      | ~ r2_hidden(D_21304,k1_relat_1(A_21303))
      | ~ v1_funct_1(A_21303)
      | ~ v1_relat_1(A_21303) ) ),
    inference(resolution,[status(thm)],[c_117387,c_52])).

tff(c_124913,plain,(
    ! [D_21305,A_21306] :
      ( ~ r2_hidden(D_21305,k1_relat_1(A_21306))
      | ~ v1_funct_1(A_21306)
      | ~ v1_relat_1(A_21306)
      | ~ r1_tarski(A_21306,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_117451,c_124867])).

tff(c_124977,plain,(
    ! [D_21305] :
      ( ~ r2_hidden(D_21305,'#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_124913])).

tff(c_124996,plain,(
    ! [D_21305] :
      ( ~ r2_hidden(D_21305,'#skF_6')
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_124977])).

tff(c_124997,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_124996])).

tff(c_125616,plain,(
    ! [A_21334,C_21335,B_21336,A_21337] :
      ( m1_subset_1(A_21334,k1_zfmisc_1(k2_zfmisc_1(C_21335,B_21336)))
      | ~ r1_tarski(k2_relat_1(A_21334),B_21336)
      | ~ r1_tarski(A_21334,k2_zfmisc_1(C_21335,A_21337)) ) ),
    inference(resolution,[status(thm)],[c_22,c_118045])).

tff(c_126645,plain,(
    ! [A_21386,B_21387] :
      ( m1_subset_1(A_21386,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_21386),B_21387)))
      | ~ r1_tarski(k2_relat_1(A_21386),B_21387)
      | ~ v1_relat_1(A_21386) ) ),
    inference(resolution,[status(thm)],[c_32,c_125616])).

tff(c_126675,plain,(
    ! [B_21387] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_21387)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_21387)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_126645])).

tff(c_126687,plain,(
    ! [B_21388] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_21388)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_21388) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_126675])).

tff(c_126698,plain,(
    ! [B_21388] :
      ( k1_relset_1('#skF_6',B_21388,'#skF_8') = k1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_21388) ) ),
    inference(resolution,[status(thm)],[c_126687,c_58])).

tff(c_126843,plain,(
    ! [B_21390] :
      ( k1_relset_1('#skF_6',B_21390,'#skF_8') = '#skF_6'
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_21390) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_126698])).

tff(c_126903,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_118025,c_126843])).

tff(c_126961,plain,(
    ! [B_21394] :
      ( r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',B_21394))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_21394) ) ),
    inference(resolution,[status(thm)],[c_126687,c_20])).

tff(c_127021,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_118025,c_126961])).

tff(c_127161,plain,(
    ! [B_21397,A_21398,A_21399] :
      ( k1_xboole_0 = B_21397
      | v1_funct_2(A_21398,A_21399,B_21397)
      | k1_relset_1(A_21399,B_21397,A_21398) != A_21399
      | ~ r1_tarski(A_21398,k2_zfmisc_1(A_21399,B_21397)) ) ),
    inference(resolution,[status(thm)],[c_22,c_118210])).

tff(c_127167,plain,
    ( k1_xboole_0 = '#skF_7'
    | v1_funct_2('#skF_8','#skF_6','#skF_7')
    | k1_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_127021,c_127161])).

tff(c_127227,plain,
    ( k1_xboole_0 = '#skF_7'
    | v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126903,c_127167])).

tff(c_127228,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_127227])).

tff(c_125249,plain,(
    ! [D_21313,A_21314,B_21315] :
      ( m1_subset_1(D_21313,k1_zfmisc_1(k2_zfmisc_1(A_21314,B_21315)))
      | ~ r1_tarski(k2_relat_1(D_21313),B_21315)
      | ~ m1_subset_1(D_21313,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_118045])).

tff(c_125471,plain,(
    ! [D_21325,A_21326,B_21327] :
      ( r1_tarski(D_21325,k2_zfmisc_1(A_21326,B_21327))
      | ~ r1_tarski(k2_relat_1(D_21325),B_21327)
      | ~ m1_subset_1(D_21325,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_125249,c_20])).

tff(c_125509,plain,(
    ! [A_21326] :
      ( r1_tarski('#skF_8',k2_zfmisc_1(A_21326,'#skF_7'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_118025,c_125471])).

tff(c_125595,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_125509])).

tff(c_126714,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_126687])).

tff(c_126726,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_125595,c_126714])).

tff(c_126756,plain,
    ( ~ v5_relat_1('#skF_8',k1_xboole_0)
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_126726])).

tff(c_126763,plain,(
    ~ v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_126756])).

tff(c_127247,plain,(
    ~ v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127228,c_126763])).

tff(c_127361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118037,c_127247])).

tff(c_127363,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_125509])).

tff(c_127376,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_127363,c_20])).

tff(c_127387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124997,c_127376])).

tff(c_127388,plain,(
    ! [D_21305] : ~ r2_hidden(D_21305,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_124996])).

tff(c_118670,plain,(
    ! [A_21058,B_21059] :
      ( r2_hidden('#skF_3'(A_21058,B_21059),k1_relat_1(A_21058))
      | r2_hidden('#skF_4'(A_21058,B_21059),B_21059)
      | k2_relat_1(A_21058) = B_21059
      | ~ v1_funct_1(A_21058)
      | ~ v1_relat_1(A_21058) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_118693,plain,(
    ! [B_21059] :
      ( r2_hidden('#skF_3'('#skF_8',B_21059),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_21059),B_21059)
      | k2_relat_1('#skF_8') = B_21059
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_118670])).

tff(c_118704,plain,(
    ! [B_21060] :
      ( r2_hidden('#skF_3'('#skF_8',B_21060),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_21060),B_21060)
      | k2_relat_1('#skF_8') = B_21060 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_118693])).

tff(c_118857,plain,(
    ! [B_21068] :
      ( ~ r1_tarski(B_21068,'#skF_4'('#skF_8',B_21068))
      | r2_hidden('#skF_3'('#skF_8',B_21068),'#skF_6')
      | k2_relat_1('#skF_8') = B_21068 ) ),
    inference(resolution,[status(thm)],[c_118704,c_52])).

tff(c_118873,plain,
    ( r2_hidden('#skF_3'('#skF_8',k2_relat_1(k1_xboole_0)),'#skF_6')
    | k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_117450,c_118857])).

tff(c_118875,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_118873])).

tff(c_118884,plain,(
    ! [B_20983] : r1_tarski(k2_relat_1('#skF_8'),B_20983) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118875,c_117450])).

tff(c_119712,plain,(
    ! [A_21098,D_21099] :
      ( ~ r1_tarski(k2_relat_1(A_21098),k1_funct_1(A_21098,D_21099))
      | ~ r2_hidden(D_21099,k1_relat_1(A_21098))
      | ~ v1_funct_1(A_21098)
      | ~ v1_relat_1(A_21098) ) ),
    inference(resolution,[status(thm)],[c_117387,c_52])).

tff(c_119719,plain,(
    ! [D_21099] :
      ( ~ r2_hidden(D_21099,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_118884,c_119712])).

tff(c_119750,plain,(
    ! [D_21100] : ~ r2_hidden(D_21100,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_119719])).

tff(c_119797,plain,(
    ! [B_21101] : r1_tarski('#skF_6',B_21101) ),
    inference(resolution,[status(thm)],[c_6,c_119750])).

tff(c_118882,plain,(
    ! [B_20984] :
      ( k2_relat_1('#skF_8') = B_20984
      | ~ r1_tarski(B_20984,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118875,c_118875,c_117510])).

tff(c_119844,plain,(
    k2_relat_1('#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_119797,c_118882])).

tff(c_119881,plain,(
    k2_zfmisc_1('#skF_6','#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119844,c_105328])).

tff(c_119788,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_119750])).

tff(c_118878,plain,(
    ! [A_15613] : k2_relat_1(k2_zfmisc_1(A_15613,k2_relat_1('#skF_8'))) = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118875,c_118875,c_117731])).

tff(c_119862,plain,(
    ! [A_15613] : k2_relat_1(k2_zfmisc_1(A_15613,'#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119844,c_119844,c_118878])).

tff(c_120391,plain,(
    ! [A_21112] : k2_relat_1(k2_zfmisc_1(A_21112,'#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119844,c_119844,c_118878])).

tff(c_120469,plain,(
    ! [A_21112] :
      ( r1_tarski(k2_zfmisc_1(A_21112,'#skF_6'),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21112,'#skF_6')),'#skF_6'))
      | ~ v1_relat_1(k2_zfmisc_1(A_21112,'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120391,c_32])).

tff(c_121882,plain,(
    ! [A_21190] : r1_tarski(k2_zfmisc_1(A_21190,'#skF_6'),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21190,'#skF_6')),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_120469])).

tff(c_121890,plain,(
    ! [A_21190,B_21010] :
      ( m1_subset_1(k2_zfmisc_1(A_21190,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21190,'#skF_6')),B_21010)))
      | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(A_21190,'#skF_6')),B_21010) ) ),
    inference(resolution,[status(thm)],[c_121882,c_118055])).

tff(c_123548,plain,(
    ! [A_21241,B_21242] : m1_subset_1(k2_zfmisc_1(A_21241,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21241,'#skF_6')),B_21242))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119788,c_119862,c_121890])).

tff(c_123571,plain,(
    ! [B_21242] : m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1('#skF_6','#skF_6')),B_21242))) ),
    inference(superposition,[status(thm),theory(equality)],[c_119881,c_123548])).

tff(c_123883,plain,(
    ! [B_21255] : m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_21255))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_119881,c_123571])).

tff(c_123894,plain,(
    ! [B_21255] : k1_relset_1('#skF_6',B_21255,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_123883,c_58])).

tff(c_123915,plain,(
    ! [B_21255] : k1_relset_1('#skF_6',B_21255,'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_123894])).

tff(c_123964,plain,(
    ! [B_21257] : r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',B_21257)) ),
    inference(resolution,[status(thm)],[c_123883,c_20])).

tff(c_123967,plain,(
    ! [B_21257] :
      ( k1_xboole_0 = B_21257
      | v1_funct_2('#skF_8','#skF_6',B_21257)
      | k1_relset_1('#skF_6',B_21257,'#skF_8') != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_123964,c_118224])).

tff(c_124012,plain,(
    ! [B_21261] :
      ( k1_xboole_0 = B_21261
      | v1_funct_2('#skF_8','#skF_6',B_21261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123915,c_123967])).

tff(c_124024,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_124012,c_167])).

tff(c_118703,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_118665])).

tff(c_124049,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124024,c_118703])).

tff(c_124090,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_124049])).

tff(c_124091,plain,(
    r2_hidden('#skF_3'('#skF_8',k2_relat_1(k1_xboole_0)),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_118873])).

tff(c_127395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127388,c_124091])).

tff(c_127397,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_118665])).

tff(c_134035,plain,(
    ! [A_21659,C_21660,B_21661,A_21662] :
      ( m1_subset_1(A_21659,k1_zfmisc_1(k2_zfmisc_1(C_21660,B_21661)))
      | ~ r1_tarski(k2_relat_1(A_21659),B_21661)
      | ~ r1_tarski(A_21659,k2_zfmisc_1(C_21660,A_21662)) ) ),
    inference(resolution,[status(thm)],[c_22,c_118045])).

tff(c_135664,plain,(
    ! [A_21751,B_21752] :
      ( m1_subset_1(A_21751,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_21751),B_21752)))
      | ~ r1_tarski(k2_relat_1(A_21751),B_21752)
      | ~ v1_relat_1(A_21751) ) ),
    inference(resolution,[status(thm)],[c_32,c_134035])).

tff(c_135706,plain,(
    ! [A_21753] :
      ( m1_subset_1(A_21753,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(A_21753),k1_xboole_0)
      | ~ v1_relat_1(A_21753) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_135664])).

tff(c_135710,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_118508,c_135706])).

tff(c_135728,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127397,c_82,c_135710])).

tff(c_135730,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134689,c_135728])).

tff(c_135732,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_134350])).

tff(c_135745,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_135732,c_20])).

tff(c_135756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133305,c_135745])).

tff(c_135757,plain,(
    ! [D_21628] : ~ r2_hidden(D_21628,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_133304])).

tff(c_127398,plain,(
    ! [B_21400] :
      ( r2_hidden('#skF_3'('#skF_8',B_21400),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_21400),B_21400)
      | k2_relat_1('#skF_8') = B_21400 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_118693])).

tff(c_127613,plain,(
    ! [B_21412] :
      ( ~ r1_tarski(B_21412,'#skF_4'('#skF_8',B_21412))
      | r2_hidden('#skF_3'('#skF_8',B_21412),'#skF_6')
      | k2_relat_1('#skF_8') = B_21412 ) ),
    inference(resolution,[status(thm)],[c_127398,c_52])).

tff(c_127629,plain,
    ( r2_hidden('#skF_3'('#skF_8',k2_relat_1(k1_xboole_0)),'#skF_6')
    | k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_117450,c_127613])).

tff(c_127695,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_127629])).

tff(c_127704,plain,(
    ! [B_20983] : r1_tarski(k2_relat_1('#skF_8'),B_20983) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127695,c_117450])).

tff(c_128299,plain,(
    ! [A_21436,D_21437] :
      ( ~ r1_tarski(k2_relat_1(A_21436),k1_funct_1(A_21436,D_21437))
      | ~ r2_hidden(D_21437,k1_relat_1(A_21436))
      | ~ v1_funct_1(A_21436)
      | ~ v1_relat_1(A_21436) ) ),
    inference(resolution,[status(thm)],[c_117387,c_52])).

tff(c_128306,plain,(
    ! [D_21437] :
      ( ~ r2_hidden(D_21437,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_127704,c_128299])).

tff(c_128337,plain,(
    ! [D_21438] : ~ r2_hidden(D_21438,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_128306])).

tff(c_128373,plain,(
    ! [B_21439] : r1_tarski('#skF_6',B_21439) ),
    inference(resolution,[status(thm)],[c_6,c_128337])).

tff(c_127702,plain,(
    ! [B_20984] :
      ( k2_relat_1('#skF_8') = B_20984
      | ~ r1_tarski(B_20984,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127695,c_127695,c_117510])).

tff(c_128422,plain,(
    k2_relat_1('#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_128373,c_127702])).

tff(c_128456,plain,(
    k2_zfmisc_1('#skF_6','#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128422,c_105328])).

tff(c_128366,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_128337])).

tff(c_127698,plain,(
    ! [A_15613] : k2_relat_1(k2_zfmisc_1(A_15613,k2_relat_1('#skF_8'))) = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127695,c_127695,c_117731])).

tff(c_128436,plain,(
    ! [A_15613] : k2_relat_1(k2_zfmisc_1(A_15613,'#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128422,c_128422,c_127698])).

tff(c_128899,plain,(
    ! [A_21447] : k2_relat_1(k2_zfmisc_1(A_21447,'#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128422,c_128422,c_127698])).

tff(c_128968,plain,(
    ! [A_21447] :
      ( r1_tarski(k2_zfmisc_1(A_21447,'#skF_6'),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21447,'#skF_6')),'#skF_6'))
      | ~ v1_relat_1(k2_zfmisc_1(A_21447,'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128899,c_32])).

tff(c_130499,plain,(
    ! [A_21531] : r1_tarski(k2_zfmisc_1(A_21531,'#skF_6'),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21531,'#skF_6')),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_128968])).

tff(c_130507,plain,(
    ! [A_21531,B_21010] :
      ( m1_subset_1(k2_zfmisc_1(A_21531,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21531,'#skF_6')),B_21010)))
      | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(A_21531,'#skF_6')),B_21010) ) ),
    inference(resolution,[status(thm)],[c_130499,c_118055])).

tff(c_131971,plain,(
    ! [A_21577,B_21578] : m1_subset_1(k2_zfmisc_1(A_21577,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21577,'#skF_6')),B_21578))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128366,c_128436,c_130507])).

tff(c_131994,plain,(
    ! [B_21578] : m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1('#skF_6','#skF_6')),B_21578))) ),
    inference(superposition,[status(thm),theory(equality)],[c_128456,c_131971])).

tff(c_132292,plain,(
    ! [B_21591] : m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_21591))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_128456,c_131994])).

tff(c_132303,plain,(
    ! [B_21591] : k1_relset_1('#skF_6',B_21591,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_132292,c_58])).

tff(c_132324,plain,(
    ! [B_21591] : k1_relset_1('#skF_6',B_21591,'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_132303])).

tff(c_132319,plain,(
    ! [B_21591] :
      ( k1_xboole_0 = B_21591
      | v1_funct_2('#skF_8','#skF_6',B_21591)
      | k1_relset_1('#skF_6',B_21591,'#skF_8') != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_132292,c_68])).

tff(c_132976,plain,(
    ! [B_21616] :
      ( k1_xboole_0 = B_21616
      | v1_funct_2('#skF_8','#skF_6',B_21616) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132324,c_132319])).

tff(c_132988,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_132976,c_167])).

tff(c_127446,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(resolution,[status(thm)],[c_127397,c_8])).

tff(c_127485,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_127446])).

tff(c_133019,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132988,c_127485])).

tff(c_133061,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_133019])).

tff(c_133062,plain,(
    r2_hidden('#skF_3'('#skF_8',k2_relat_1(k1_xboole_0)),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_127629])).

tff(c_135764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135757,c_133062])).

tff(c_135765,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_127446])).

tff(c_135863,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135765,c_119])).

tff(c_135868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118669,c_135863])).

tff(c_135870,plain,(
    v1_relat_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_118668])).

tff(c_117601,plain,(
    ! [A_20993,B_20994] :
      ( r1_tarski(k2_relat_1(A_20993),B_20994)
      | ~ v1_relat_1(A_20993)
      | ~ r1_tarski(A_20993,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_286,c_117424])).

tff(c_117650,plain,(
    ! [A_20993] :
      ( k2_relat_1(k1_xboole_0) = k2_relat_1(A_20993)
      | ~ v1_relat_1(A_20993)
      | ~ r1_tarski(A_20993,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_117601,c_117510])).

tff(c_144053,plain,
    ( k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_144050,c_117650])).

tff(c_144064,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135870,c_144053])).

tff(c_117737,plain,(
    ! [A_20997] : k2_relat_1(k2_zfmisc_1(A_20997,k2_relat_1(k1_xboole_0))) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_117712])).

tff(c_117792,plain,(
    ! [A_20997,A_12] :
      ( v5_relat_1(k2_zfmisc_1(A_20997,k2_relat_1(k1_xboole_0)),A_12)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),A_12)
      | ~ v1_relat_1(k2_zfmisc_1(A_20997,k2_relat_1(k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117737,c_24])).

tff(c_117834,plain,(
    ! [A_20997,A_12] : v5_relat_1(k2_zfmisc_1(A_20997,k2_relat_1(k1_xboole_0)),A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_117450,c_117792])).

tff(c_144145,plain,(
    ! [A_20997,A_12] : v5_relat_1(k2_zfmisc_1(A_20997,k2_relat_1('#skF_7')),A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144064,c_117834])).

tff(c_144629,plain,(
    ! [A_22097] : k2_relat_1(k2_zfmisc_1(A_22097,k2_relat_1('#skF_7'))) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144064,c_144064,c_117731])).

tff(c_144689,plain,(
    ! [C_19,A_16,A_22097] :
      ( r2_hidden(C_19,A_16)
      | ~ r2_hidden(C_19,k2_relat_1('#skF_7'))
      | ~ v5_relat_1(k2_zfmisc_1(A_22097,k2_relat_1('#skF_7')),A_16)
      | ~ v1_relat_1(k2_zfmisc_1(A_22097,k2_relat_1('#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144629,c_30])).

tff(c_144831,plain,(
    ! [C_22104,A_22105] :
      ( r2_hidden(C_22104,A_22105)
      | ~ r2_hidden(C_22104,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_144145,c_144689])).

tff(c_144858,plain,(
    ! [A_22105] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_7')),A_22105)
      | r2_hidden('#skF_3'('#skF_8',k2_relat_1('#skF_7')),'#skF_6')
      | k2_relat_1('#skF_7') = k2_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_144104,c_144831])).

tff(c_145251,plain,(
    k2_relat_1('#skF_7') = k2_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_144858])).

tff(c_144152,plain,(
    ! [B_20983] : r1_tarski(k2_relat_1('#skF_7'),B_20983) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144064,c_117450])).

tff(c_145428,plain,(
    ! [B_22125] : r1_tarski(k2_relat_1('#skF_8'),B_22125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145251,c_144152])).

tff(c_117397,plain,(
    ! [A_20977,D_20978] :
      ( ~ r1_tarski(k2_relat_1(A_20977),k1_funct_1(A_20977,D_20978))
      | ~ r2_hidden(D_20978,k1_relat_1(A_20977))
      | ~ v1_funct_1(A_20977)
      | ~ v1_relat_1(A_20977) ) ),
    inference(resolution,[status(thm)],[c_117387,c_52])).

tff(c_145432,plain,(
    ! [D_20978] :
      ( ~ r2_hidden(D_20978,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_145428,c_117397])).

tff(c_145490,plain,(
    ! [D_20978] : ~ r2_hidden(D_20978,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_145432])).

tff(c_145726,plain,(
    ! [B_22132] :
      ( r2_hidden('#skF_4'('#skF_8',B_22132),B_22132)
      | k2_relat_1('#skF_8') = B_22132 ) ),
    inference(negUnitSimplification,[status(thm)],[c_145490,c_144104])).

tff(c_145745,plain,(
    k2_relat_1('#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_145726,c_145490])).

tff(c_145770,plain,(
    k2_zfmisc_1('#skF_6','#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145745,c_105328])).

tff(c_146071,plain,(
    ! [A_22133] :
      ( k2_zfmisc_1(k1_relat_1(A_22133),k2_relat_1(A_22133)) = A_22133
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_22133),k2_relat_1(A_22133)),A_22133)
      | ~ v1_relat_1(A_22133) ) ),
    inference(resolution,[status(thm)],[c_239,c_8])).

tff(c_146083,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_8'),k2_relat_1('#skF_8')) = '#skF_8'
    | ~ r1_tarski(k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8')),'#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_146071])).

tff(c_146091,plain,
    ( k2_zfmisc_1('#skF_6','#skF_6') = '#skF_8'
    | ~ r1_tarski(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_145745,c_145745,c_78,c_146083])).

tff(c_146248,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_146091])).

tff(c_146345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_145770,c_146248])).

tff(c_146346,plain,(
    k2_zfmisc_1('#skF_6','#skF_6') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_146091])).

tff(c_105417,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_105420,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_105417])).

tff(c_105424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_105420])).

tff(c_105426,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_145519,plain,(
    ! [D_22126] : ~ r2_hidden(D_22126,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_145432])).

tff(c_145562,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_145519])).

tff(c_145263,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145251,c_144064])).

tff(c_146092,plain,(
    k2_relat_1(k1_xboole_0) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145745,c_145263])).

tff(c_150025,plain,(
    ! [D_22286,A_22287,B_22288] :
      ( r1_tarski(D_22286,k2_zfmisc_1(A_22287,B_22288))
      | ~ r1_tarski(k2_relat_1(D_22286),B_22288)
      | ~ m1_subset_1(D_22286,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_145095,c_20])).

tff(c_150033,plain,(
    ! [A_22287,B_22288] :
      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(A_22287,B_22288))
      | ~ r1_tarski('#skF_6',B_22288)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146092,c_150025])).

tff(c_150068,plain,(
    ! [A_22289,B_22290] : r1_tarski(k1_xboole_0,k2_zfmisc_1(A_22289,B_22290)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105426,c_145562,c_150033])).

tff(c_150089,plain,(
    r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_146346,c_150068])).

tff(c_150118,plain,
    ( k1_xboole_0 = '#skF_8'
    | ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_150089,c_8])).

tff(c_150129,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_105358,c_150118])).

tff(c_146417,plain,(
    ! [A_22138,C_22139,B_22140,A_22141] :
      ( m1_subset_1(A_22138,k1_zfmisc_1(k2_zfmisc_1(C_22139,B_22140)))
      | ~ r1_tarski(k2_relat_1(A_22138),B_22140)
      | ~ r1_tarski(A_22138,k2_zfmisc_1(C_22139,A_22141)) ) ),
    inference(resolution,[status(thm)],[c_22,c_118045])).

tff(c_150213,plain,(
    ! [A_22295,B_22296] :
      ( m1_subset_1(A_22295,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_22295),B_22296)))
      | ~ r1_tarski(k2_relat_1(A_22295),B_22296)
      | ~ v1_relat_1(A_22295) ) ),
    inference(resolution,[status(thm)],[c_32,c_146417])).

tff(c_150243,plain,(
    ! [B_22296] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_22296)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_22296)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_150213])).

tff(c_150255,plain,(
    ! [B_22297] : m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_22297))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_145562,c_145745,c_150243])).

tff(c_150280,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_150255])).

tff(c_150331,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_150280,c_20])).

tff(c_150343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150129,c_150331])).

tff(c_150345,plain,(
    k2_relat_1('#skF_7') != k2_relat_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_144858])).

tff(c_144294,plain,(
    ! [B_22079] :
      ( r2_hidden('#skF_3'('#skF_8',B_22079),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_22079),B_22079)
      | k2_relat_1('#skF_8') = B_22079 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_144095])).

tff(c_144609,plain,(
    ! [B_22096] :
      ( ~ r1_tarski(B_22096,'#skF_4'('#skF_8',B_22096))
      | r2_hidden('#skF_3'('#skF_8',B_22096),'#skF_6')
      | k2_relat_1('#skF_8') = B_22096 ) ),
    inference(resolution,[status(thm)],[c_144294,c_52])).

tff(c_144622,plain,
    ( r2_hidden('#skF_3'('#skF_8',k2_relat_1('#skF_7')),'#skF_6')
    | k2_relat_1('#skF_7') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_144152,c_144609])).

tff(c_150623,plain,(
    r2_hidden('#skF_3'('#skF_8',k2_relat_1('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_150345,c_144622])).

tff(c_155014,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155007,c_150623])).

tff(c_155016,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_105347])).

tff(c_155132,plain,(
    ! [A_73] :
      ( v1_funct_2('#skF_8',A_73,'#skF_8')
      | A_73 = '#skF_8'
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155016,c_155016,c_155016,c_155016,c_155016,c_88])).

tff(c_155133,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_155132])).

tff(c_155136,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_22,c_155133])).

tff(c_155140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_155136])).

tff(c_155142,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_155132])).

tff(c_155024,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_8',B_9) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155016,c_155016,c_18])).

tff(c_155347,plain,(
    ! [A_22543,B_22544,C_22545] :
      ( k1_relset_1(A_22543,B_22544,C_22545) = k1_relat_1(C_22545)
      | ~ m1_subset_1(C_22545,k1_zfmisc_1(k2_zfmisc_1(A_22543,B_22544))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_155399,plain,(
    ! [B_22548,C_22549] :
      ( k1_relset_1('#skF_8',B_22548,C_22549) = k1_relat_1(C_22549)
      | ~ m1_subset_1(C_22549,k1_zfmisc_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155024,c_155347])).

tff(c_155401,plain,(
    ! [B_22548] : k1_relset_1('#skF_8',B_22548,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_155142,c_155399])).

tff(c_155406,plain,(
    ! [B_22548] : k1_relset_1('#skF_8',B_22548,'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_155401])).

tff(c_155487,plain,(
    ! [C_22561,B_22562] :
      ( v1_funct_2(C_22561,'#skF_8',B_22562)
      | k1_relset_1('#skF_8',B_22562,C_22561) != '#skF_8'
      | ~ m1_subset_1(C_22561,k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155016,c_155016,c_155016,c_155016,c_85])).

tff(c_155489,plain,(
    ! [B_22562] :
      ( v1_funct_2('#skF_8','#skF_8',B_22562)
      | k1_relset_1('#skF_8',B_22562,'#skF_8') != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_155142,c_155487])).

tff(c_155494,plain,(
    ! [B_22562] :
      ( v1_funct_2('#skF_8','#skF_8',B_22562)
      | '#skF_6' != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155406,c_155489])).

tff(c_155496,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_155494])).

tff(c_155017,plain,(
    ! [A_10,B_127] :
      ( v5_relat_1(A_10,B_127)
      | ~ r1_tarski(A_10,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155016,c_286])).

tff(c_155015,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_105347])).

tff(c_155102,plain,
    ( '#skF_6' = '#skF_8'
    | k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155016,c_155016,c_155015])).

tff(c_155103,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_155102])).

tff(c_155112,plain,(
    ! [A_12] :
      ( r1_tarski('#skF_8',A_12)
      | ~ v5_relat_1('#skF_8',A_12)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155103,c_26])).

tff(c_155160,plain,(
    ! [A_22517] :
      ( r1_tarski('#skF_8',A_22517)
      | ~ v5_relat_1('#skF_8',A_22517) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_155112])).

tff(c_155164,plain,(
    ! [B_127] :
      ( r1_tarski('#skF_8',B_127)
      | ~ r1_tarski('#skF_8','#skF_8') ) ),
    inference(resolution,[status(thm)],[c_155017,c_155160])).

tff(c_155174,plain,(
    ! [B_127] : r1_tarski('#skF_8',B_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_155164])).

tff(c_155810,plain,(
    ! [A_22598,D_22599] :
      ( r2_hidden(k1_funct_1(A_22598,D_22599),k2_relat_1(A_22598))
      | ~ r2_hidden(D_22599,k1_relat_1(A_22598))
      | ~ v1_funct_1(A_22598)
      | ~ v1_relat_1(A_22598) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_155820,plain,(
    ! [D_22599] :
      ( r2_hidden(k1_funct_1('#skF_8',D_22599),'#skF_8')
      | ~ r2_hidden(D_22599,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155103,c_155810])).

tff(c_155826,plain,(
    ! [D_22600] :
      ( r2_hidden(k1_funct_1('#skF_8',D_22600),'#skF_8')
      | ~ r2_hidden(D_22600,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_155820])).

tff(c_155833,plain,(
    ! [D_22600] :
      ( ~ r1_tarski('#skF_8',k1_funct_1('#skF_8',D_22600))
      | ~ r2_hidden(D_22600,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_155826,c_52])).

tff(c_155841,plain,(
    ! [D_22601] : ~ r2_hidden(D_22601,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155174,c_155833])).

tff(c_155852,plain,(
    ! [B_22602] : r1_tarski('#skF_6',B_22602) ),
    inference(resolution,[status(thm)],[c_6,c_155841])).

tff(c_155181,plain,(
    ! [B_22518] : r1_tarski('#skF_8',B_22518) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_155164])).

tff(c_155201,plain,(
    ! [B_22518] :
      ( B_22518 = '#skF_8'
      | ~ r1_tarski(B_22518,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_155181,c_8])).

tff(c_155874,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_155852,c_155201])).

tff(c_155893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155496,c_155874])).

tff(c_155894,plain,(
    ! [B_22562] : v1_funct_2('#skF_8','#skF_8',B_22562) ),
    inference(splitRight,[status(thm)],[c_155494])).

tff(c_155895,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_155494])).

tff(c_155923,plain,(
    ~ v1_funct_2('#skF_8','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155895,c_167])).

tff(c_155954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155894,c_155923])).

tff(c_155955,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_155102])).

tff(c_155963,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155955,c_78])).

tff(c_155969,plain,(
    ! [A_73] :
      ( v1_funct_2('#skF_8',A_73,'#skF_8')
      | A_73 = '#skF_8'
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155016,c_155016,c_155016,c_155016,c_155016,c_88])).

tff(c_155970,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_155969])).

tff(c_155995,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_22,c_155970])).

tff(c_155999,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_155995])).

tff(c_156001,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_155969])).

tff(c_156061,plain,(
    ! [A_22618,B_22619,C_22620] :
      ( k1_relset_1(A_22618,B_22619,C_22620) = k1_relat_1(C_22620)
      | ~ m1_subset_1(C_22620,k1_zfmisc_1(k2_zfmisc_1(A_22618,B_22619))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_156167,plain,(
    ! [B_22642,C_22643] :
      ( k1_relset_1('#skF_8',B_22642,C_22643) = k1_relat_1(C_22643)
      | ~ m1_subset_1(C_22643,k1_zfmisc_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155024,c_156061])).

tff(c_156169,plain,(
    ! [B_22642] : k1_relset_1('#skF_8',B_22642,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_156001,c_156167])).

tff(c_156174,plain,(
    ! [B_22642] : k1_relset_1('#skF_8',B_22642,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155963,c_156169])).

tff(c_156192,plain,(
    ! [C_22645,B_22646] :
      ( v1_funct_2(C_22645,'#skF_8',B_22646)
      | k1_relset_1('#skF_8',B_22646,C_22645) != '#skF_8'
      | ~ m1_subset_1(C_22645,k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155016,c_155016,c_155016,c_155016,c_85])).

tff(c_156194,plain,(
    ! [B_22646] :
      ( v1_funct_2('#skF_8','#skF_8',B_22646)
      | k1_relset_1('#skF_8',B_22646,'#skF_8') != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_156001,c_156192])).

tff(c_156200,plain,(
    ! [B_22646] : v1_funct_2('#skF_8','#skF_8',B_22646) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156174,c_156194])).

tff(c_155960,plain,(
    ~ v1_funct_2('#skF_8','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155955,c_167])).

tff(c_156204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156200,c_155960])).

tff(c_156205,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_162346,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_162326,c_156205])).

tff(c_162365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157569,c_162346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.00/16.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.87/17.20  
% 27.87/17.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.87/17.20  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 27.87/17.20  
% 27.87/17.20  %Foreground sorts:
% 27.87/17.20  
% 27.87/17.20  
% 27.87/17.20  %Background operators:
% 27.87/17.20  
% 27.87/17.20  
% 27.87/17.20  %Foreground operators:
% 27.87/17.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 27.87/17.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.87/17.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.87/17.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 27.87/17.20  tff('#skF_7', type, '#skF_7': $i).
% 27.87/17.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 27.87/17.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.87/17.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 27.87/17.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 27.87/17.20  tff('#skF_6', type, '#skF_6': $i).
% 27.87/17.20  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 27.87/17.20  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 27.87/17.20  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 27.87/17.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 27.87/17.20  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 27.87/17.20  tff('#skF_8', type, '#skF_8': $i).
% 27.87/17.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.87/17.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 27.87/17.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 27.87/17.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.87/17.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 27.87/17.20  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 27.87/17.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 27.87/17.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 27.87/17.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 27.87/17.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 27.87/17.20  
% 27.93/17.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 27.93/17.29  tff(f_141, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 27.93/17.29  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 27.93/17.29  tff(f_69, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 27.93/17.29  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 27.93/17.29  tff(f_105, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 27.93/17.29  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 27.93/17.29  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 27.93/17.29  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 27.93/17.29  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 27.93/17.29  tff(f_89, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 27.93/17.29  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 27.93/17.29  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 27.93/17.29  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 27.93/17.29  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 27.93/17.29  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.93/17.29  tff(c_82, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_141])).
% 27.93/17.29  tff(c_80, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_141])).
% 27.93/17.29  tff(c_78, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_141])).
% 27.93/17.29  tff(c_157505, plain, (![A_22798, C_22799]: (r2_hidden('#skF_5'(A_22798, k2_relat_1(A_22798), C_22799), k1_relat_1(A_22798)) | ~r2_hidden(C_22799, k2_relat_1(A_22798)) | ~v1_funct_1(A_22798) | ~v1_relat_1(A_22798))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.29  tff(c_157516, plain, (![C_22799]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_22799), '#skF_6') | ~r2_hidden(C_22799, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_157505])).
% 27.93/17.29  tff(c_157523, plain, (![C_22800]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_22800), '#skF_6') | ~r2_hidden(C_22800, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_157516])).
% 27.93/17.29  tff(c_157291, plain, (![A_22784, C_22785]: (k1_funct_1(A_22784, '#skF_5'(A_22784, k2_relat_1(A_22784), C_22785))=C_22785 | ~r2_hidden(C_22785, k2_relat_1(A_22784)) | ~v1_funct_1(A_22784) | ~v1_relat_1(A_22784))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.29  tff(c_76, plain, (![D_77]: (r2_hidden(k1_funct_1('#skF_8', D_77), '#skF_7') | ~r2_hidden(D_77, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 27.93/17.29  tff(c_157321, plain, (![C_22785]: (r2_hidden(C_22785, '#skF_7') | ~r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_22785), '#skF_6') | ~r2_hidden(C_22785, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_157291, c_76])).
% 27.93/17.29  tff(c_157340, plain, (![C_22785]: (r2_hidden(C_22785, '#skF_7') | ~r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_22785), '#skF_6') | ~r2_hidden(C_22785, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_157321])).
% 27.93/17.29  tff(c_157535, plain, (![C_22801]: (r2_hidden(C_22801, '#skF_7') | ~r2_hidden(C_22801, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_157523, c_157340])).
% 27.93/17.29  tff(c_157558, plain, (![B_22802]: (r2_hidden('#skF_1'(k2_relat_1('#skF_8'), B_22802), '#skF_7') | r1_tarski(k2_relat_1('#skF_8'), B_22802))), inference(resolution, [status(thm)], [c_6, c_157535])).
% 27.93/17.29  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.93/17.29  tff(c_157569, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_157558, c_4])).
% 27.93/17.29  tff(c_156218, plain, (![A_22650]: (r1_tarski(A_22650, k2_zfmisc_1(k1_relat_1(A_22650), k2_relat_1(A_22650))) | ~v1_relat_1(A_22650))), inference(cnfTransformation, [status(thm)], [f_69])).
% 27.93/17.29  tff(c_156223, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8'))) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_78, c_156218])).
% 27.93/17.29  tff(c_156226, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_156223])).
% 27.93/17.29  tff(c_22, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 27.93/17.29  tff(c_157591, plain, (![D_22805, C_22806, B_22807, A_22808]: (m1_subset_1(D_22805, k1_zfmisc_1(k2_zfmisc_1(C_22806, B_22807))) | ~r1_tarski(k2_relat_1(D_22805), B_22807) | ~m1_subset_1(D_22805, k1_zfmisc_1(k2_zfmisc_1(C_22806, A_22808))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 27.93/17.29  tff(c_162193, plain, (![A_23015, C_23016, B_23017, A_23018]: (m1_subset_1(A_23015, k1_zfmisc_1(k2_zfmisc_1(C_23016, B_23017))) | ~r1_tarski(k2_relat_1(A_23015), B_23017) | ~r1_tarski(A_23015, k2_zfmisc_1(C_23016, A_23018)))), inference(resolution, [status(thm)], [c_22, c_157591])).
% 27.93/17.29  tff(c_162326, plain, (![B_23025]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_23025))) | ~r1_tarski(k2_relat_1('#skF_8'), B_23025))), inference(resolution, [status(thm)], [c_156226, c_162193])).
% 27.93/17.29  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.93/17.29  tff(c_18, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.93/17.29  tff(c_264, plain, (![C_122, B_123, A_124]: (v5_relat_1(C_122, B_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 27.93/17.29  tff(c_282, plain, (![C_126, B_127]: (v5_relat_1(C_126, B_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_264])).
% 27.93/17.29  tff(c_286, plain, (![A_10, B_127]: (v5_relat_1(A_10, B_127) | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_282])).
% 27.93/17.29  tff(c_212, plain, (![B_116, A_117]: (r1_tarski(k2_relat_1(B_116), A_117) | ~v5_relat_1(B_116, A_117) | ~v1_relat_1(B_116))), inference(cnfTransformation, [status(thm)], [f_54])).
% 27.93/17.29  tff(c_143, plain, (![A_94, B_95]: (r2_hidden('#skF_1'(A_94, B_95), A_94) | r1_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.93/17.29  tff(c_52, plain, (![B_62, A_61]: (~r1_tarski(B_62, A_61) | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_89])).
% 27.93/17.29  tff(c_153, plain, (![A_94, B_95]: (~r1_tarski(A_94, '#skF_1'(A_94, B_95)) | r1_tarski(A_94, B_95))), inference(resolution, [status(thm)], [c_143, c_52])).
% 27.93/17.29  tff(c_117424, plain, (![B_20982, B_20983]: (r1_tarski(k2_relat_1(B_20982), B_20983) | ~v5_relat_1(B_20982, '#skF_1'(k2_relat_1(B_20982), B_20983)) | ~v1_relat_1(B_20982))), inference(resolution, [status(thm)], [c_212, c_153])).
% 27.93/17.29  tff(c_117451, plain, (![A_10, B_20983]: (r1_tarski(k2_relat_1(A_10), B_20983) | ~v1_relat_1(A_10) | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_286, c_117424])).
% 27.93/17.29  tff(c_117387, plain, (![A_20977, D_20978]: (r2_hidden(k1_funct_1(A_20977, D_20978), k2_relat_1(A_20977)) | ~r2_hidden(D_20978, k1_relat_1(A_20977)) | ~v1_funct_1(A_20977) | ~v1_relat_1(A_20977))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.29  tff(c_145015, plain, (![A_22111, D_22112]: (~r1_tarski(k2_relat_1(A_22111), k1_funct_1(A_22111, D_22112)) | ~r2_hidden(D_22112, k1_relat_1(A_22111)) | ~v1_funct_1(A_22111) | ~v1_relat_1(A_22111))), inference(resolution, [status(thm)], [c_117387, c_52])).
% 27.93/17.29  tff(c_150784, plain, (![D_22320, A_22321]: (~r2_hidden(D_22320, k1_relat_1(A_22321)) | ~v1_funct_1(A_22321) | ~v1_relat_1(A_22321) | ~r1_tarski(A_22321, k1_xboole_0))), inference(resolution, [status(thm)], [c_117451, c_145015])).
% 27.93/17.29  tff(c_150852, plain, (![D_22320]: (~r2_hidden(D_22320, '#skF_6') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_78, c_150784])).
% 27.93/17.29  tff(c_150872, plain, (![D_22320]: (~r2_hidden(D_22320, '#skF_6') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_150852])).
% 27.93/17.29  tff(c_150873, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_150872])).
% 27.93/17.29  tff(c_142084, plain, (![A_22004, D_22005]: (~r1_tarski(k2_relat_1(A_22004), k1_funct_1(A_22004, D_22005)) | ~r2_hidden(D_22005, k1_relat_1(A_22004)) | ~v1_funct_1(A_22004) | ~v1_relat_1(A_22004))), inference(resolution, [status(thm)], [c_117387, c_52])).
% 27.93/17.29  tff(c_142146, plain, (![D_22006, A_22007]: (~r2_hidden(D_22006, k1_relat_1(A_22007)) | ~v1_funct_1(A_22007) | ~v1_relat_1(A_22007) | ~r1_tarski(A_22007, k1_xboole_0))), inference(resolution, [status(thm)], [c_117451, c_142084])).
% 27.93/17.29  tff(c_142210, plain, (![D_22006]: (~r2_hidden(D_22006, '#skF_6') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_78, c_142146])).
% 27.93/17.29  tff(c_142229, plain, (![D_22006]: (~r2_hidden(D_22006, '#skF_6') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_142210])).
% 27.93/17.29  tff(c_142230, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_142229])).
% 27.93/17.29  tff(c_117544, plain, (![A_20988, C_20989]: (r2_hidden('#skF_5'(A_20988, k2_relat_1(A_20988), C_20989), k1_relat_1(A_20988)) | ~r2_hidden(C_20989, k2_relat_1(A_20988)) | ~v1_funct_1(A_20988) | ~v1_relat_1(A_20988))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.29  tff(c_117555, plain, (![C_20989]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_20989), '#skF_6') | ~r2_hidden(C_20989, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_117544])).
% 27.93/17.29  tff(c_117561, plain, (![C_20989]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_20989), '#skF_6') | ~r2_hidden(C_20989, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_117555])).
% 27.93/17.29  tff(c_117881, plain, (![A_21000, C_21001]: (k1_funct_1(A_21000, '#skF_5'(A_21000, k2_relat_1(A_21000), C_21001))=C_21001 | ~r2_hidden(C_21001, k2_relat_1(A_21000)) | ~v1_funct_1(A_21000) | ~v1_relat_1(A_21000))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.29  tff(c_117915, plain, (![C_21001]: (r2_hidden(C_21001, '#skF_7') | ~r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_21001), '#skF_6') | ~r2_hidden(C_21001, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_117881, c_76])).
% 27.93/17.29  tff(c_117986, plain, (![C_21005]: (r2_hidden(C_21005, '#skF_7') | ~r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_21005), '#skF_6') | ~r2_hidden(C_21005, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_117915])).
% 27.93/17.29  tff(c_117991, plain, (![C_21006]: (r2_hidden(C_21006, '#skF_7') | ~r2_hidden(C_21006, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_117561, c_117986])).
% 27.93/17.29  tff(c_118014, plain, (![B_21007]: (r2_hidden('#skF_1'(k2_relat_1('#skF_8'), B_21007), '#skF_7') | r1_tarski(k2_relat_1('#skF_8'), B_21007))), inference(resolution, [status(thm)], [c_6, c_117991])).
% 27.93/17.29  tff(c_118025, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_118014, c_4])).
% 27.93/17.29  tff(c_24, plain, (![B_13, A_12]: (v5_relat_1(B_13, A_12) | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 27.93/17.29  tff(c_118031, plain, (v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_118025, c_24])).
% 27.93/17.29  tff(c_118037, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_118031])).
% 27.93/17.29  tff(c_74, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_141])).
% 27.93/17.29  tff(c_84, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_74])).
% 27.93/17.29  tff(c_167, plain, (~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_84])).
% 27.93/17.29  tff(c_32, plain, (![A_20]: (r1_tarski(A_20, k2_zfmisc_1(k1_relat_1(A_20), k2_relat_1(A_20))) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 27.93/17.29  tff(c_118045, plain, (![D_21008, C_21009, B_21010, A_21011]: (m1_subset_1(D_21008, k1_zfmisc_1(k2_zfmisc_1(C_21009, B_21010))) | ~r1_tarski(k2_relat_1(D_21008), B_21010) | ~m1_subset_1(D_21008, k1_zfmisc_1(k2_zfmisc_1(C_21009, A_21011))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 27.93/17.29  tff(c_142679, plain, (![A_22024, C_22025, B_22026, A_22027]: (m1_subset_1(A_22024, k1_zfmisc_1(k2_zfmisc_1(C_22025, B_22026))) | ~r1_tarski(k2_relat_1(A_22024), B_22026) | ~r1_tarski(A_22024, k2_zfmisc_1(C_22025, A_22027)))), inference(resolution, [status(thm)], [c_22, c_118045])).
% 27.93/17.29  tff(c_143537, plain, (![A_22067, B_22068]: (m1_subset_1(A_22067, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_22067), B_22068))) | ~r1_tarski(k2_relat_1(A_22067), B_22068) | ~v1_relat_1(A_22067))), inference(resolution, [status(thm)], [c_32, c_142679])).
% 27.93/17.29  tff(c_143567, plain, (![B_22068]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_22068))) | ~r1_tarski(k2_relat_1('#skF_8'), B_22068) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_143537])).
% 27.93/17.29  tff(c_143579, plain, (![B_22069]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_22069))) | ~r1_tarski(k2_relat_1('#skF_8'), B_22069))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_143567])).
% 27.93/17.29  tff(c_58, plain, (![A_66, B_67, C_68]: (k1_relset_1(A_66, B_67, C_68)=k1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 27.93/17.29  tff(c_143590, plain, (![B_22069]: (k1_relset_1('#skF_6', B_22069, '#skF_8')=k1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), B_22069))), inference(resolution, [status(thm)], [c_143579, c_58])).
% 27.93/17.29  tff(c_143718, plain, (![B_22071]: (k1_relset_1('#skF_6', B_22071, '#skF_8')='#skF_6' | ~r1_tarski(k2_relat_1('#skF_8'), B_22071))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_143590])).
% 27.93/17.29  tff(c_143761, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_118025, c_143718])).
% 27.93/17.29  tff(c_20, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 27.93/17.29  tff(c_143819, plain, (![B_22075]: (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', B_22075)) | ~r1_tarski(k2_relat_1('#skF_8'), B_22075))), inference(resolution, [status(thm)], [c_143579, c_20])).
% 27.93/17.29  tff(c_143862, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_118025, c_143819])).
% 27.93/17.29  tff(c_118210, plain, (![B_21020, C_21021, A_21022]: (k1_xboole_0=B_21020 | v1_funct_2(C_21021, A_21022, B_21020) | k1_relset_1(A_21022, B_21020, C_21021)!=A_21022 | ~m1_subset_1(C_21021, k1_zfmisc_1(k2_zfmisc_1(A_21022, B_21020))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 27.93/17.29  tff(c_118224, plain, (![B_21020, A_10, A_21022]: (k1_xboole_0=B_21020 | v1_funct_2(A_10, A_21022, B_21020) | k1_relset_1(A_21022, B_21020, A_10)!=A_21022 | ~r1_tarski(A_10, k2_zfmisc_1(A_21022, B_21020)))), inference(resolution, [status(thm)], [c_22, c_118210])).
% 27.93/17.29  tff(c_143874, plain, (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', '#skF_6', '#skF_7') | k1_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_6'), inference(resolution, [status(thm)], [c_143862, c_118224])).
% 27.93/17.29  tff(c_143894, plain, (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_143761, c_143874])).
% 27.93/17.29  tff(c_143895, plain, (k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_167, c_143894])).
% 27.93/17.29  tff(c_26, plain, (![B_13, A_12]: (r1_tarski(k2_relat_1(B_13), A_12) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 27.93/17.29  tff(c_16, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.93/17.29  tff(c_142428, plain, (![D_22012, A_22013, B_22014]: (m1_subset_1(D_22012, k1_zfmisc_1(k2_zfmisc_1(A_22013, B_22014))) | ~r1_tarski(k2_relat_1(D_22012), B_22014) | ~m1_subset_1(D_22012, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_118045])).
% 27.93/17.29  tff(c_142953, plain, (![D_22035, A_22036, B_22037]: (r1_tarski(D_22035, k2_zfmisc_1(A_22036, B_22037)) | ~r1_tarski(k2_relat_1(D_22035), B_22037) | ~m1_subset_1(D_22035, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_142428, c_20])).
% 27.93/17.29  tff(c_142991, plain, (![A_22036]: (r1_tarski('#skF_8', k2_zfmisc_1(A_22036, '#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_118025, c_142953])).
% 27.93/17.29  tff(c_143231, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_142991])).
% 27.93/17.29  tff(c_143606, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_143579])).
% 27.93/17.29  tff(c_143618, plain, (~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_143231, c_143606])).
% 27.93/17.29  tff(c_143648, plain, (~v5_relat_1('#skF_8', k1_xboole_0) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_26, c_143618])).
% 27.93/17.29  tff(c_143655, plain, (~v5_relat_1('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_143648])).
% 27.93/17.29  tff(c_143906, plain, (~v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_143895, c_143655])).
% 27.93/17.29  tff(c_144014, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118037, c_143906])).
% 27.93/17.29  tff(c_144016, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_142991])).
% 27.93/17.29  tff(c_144029, plain, (r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_144016, c_20])).
% 27.93/17.29  tff(c_144040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142230, c_144029])).
% 27.93/17.29  tff(c_144041, plain, (![D_22006]: (~r2_hidden(D_22006, '#skF_6'))), inference(splitRight, [status(thm)], [c_142229])).
% 27.93/17.29  tff(c_117, plain, (![A_81, B_82]: (v1_relat_1(k2_zfmisc_1(A_81, B_82)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 27.93/17.29  tff(c_119, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_117])).
% 27.93/17.29  tff(c_105372, plain, (![A_15611, B_15612, A_15613]: (v5_relat_1(A_15611, B_15612) | ~r1_tarski(A_15611, k2_zfmisc_1(A_15613, B_15612)))), inference(resolution, [status(thm)], [c_22, c_264])).
% 27.93/17.29  tff(c_105404, plain, (![A_15616, B_15617]: (v5_relat_1(k2_zfmisc_1(A_15616, B_15617), B_15617))), inference(resolution, [status(thm)], [c_12, c_105372])).
% 27.93/17.29  tff(c_105410, plain, (![B_9]: (v5_relat_1(k1_xboole_0, B_9))), inference(superposition, [status(thm), theory('equality')], [c_18, c_105404])).
% 27.93/17.29  tff(c_117440, plain, (![B_20983]: (r1_tarski(k2_relat_1(k1_xboole_0), B_20983) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_105410, c_117424])).
% 27.93/17.29  tff(c_117450, plain, (![B_20983]: (r1_tarski(k2_relat_1(k1_xboole_0), B_20983))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_117440])).
% 27.93/17.29  tff(c_135903, plain, (![A_21758, B_21759]: (r2_hidden('#skF_3'(A_21758, B_21759), k1_relat_1(A_21758)) | r2_hidden('#skF_4'(A_21758, B_21759), B_21759) | k2_relat_1(A_21758)=B_21759 | ~v1_funct_1(A_21758) | ~v1_relat_1(A_21758))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.29  tff(c_135927, plain, (![B_21759]: (r2_hidden('#skF_3'('#skF_8', B_21759), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_21759), B_21759) | k2_relat_1('#skF_8')=B_21759 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_135903])).
% 27.93/17.29  tff(c_135950, plain, (![B_21762]: (r2_hidden('#skF_3'('#skF_8', B_21762), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_21762), B_21762) | k2_relat_1('#skF_8')=B_21762)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_135927])).
% 27.93/17.29  tff(c_136092, plain, (![B_21767]: (~r1_tarski(B_21767, '#skF_4'('#skF_8', B_21767)) | r2_hidden('#skF_3'('#skF_8', B_21767), '#skF_6') | k2_relat_1('#skF_8')=B_21767)), inference(resolution, [status(thm)], [c_135950, c_52])).
% 27.93/17.29  tff(c_136108, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1(k1_xboole_0)), '#skF_6') | k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_117450, c_136092])).
% 27.93/17.29  tff(c_136164, plain, (k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_136108])).
% 27.93/17.29  tff(c_136173, plain, (![B_20983]: (r1_tarski(k2_relat_1('#skF_8'), B_20983))), inference(demodulation, [status(thm), theory('equality')], [c_136164, c_117450])).
% 27.93/17.29  tff(c_136927, plain, (![A_21798, D_21799]: (~r1_tarski(k2_relat_1(A_21798), k1_funct_1(A_21798, D_21799)) | ~r2_hidden(D_21799, k1_relat_1(A_21798)) | ~v1_funct_1(A_21798) | ~v1_relat_1(A_21798))), inference(resolution, [status(thm)], [c_117387, c_52])).
% 27.93/17.29  tff(c_136934, plain, (![D_21799]: (~r2_hidden(D_21799, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_136173, c_136927])).
% 27.93/17.29  tff(c_136965, plain, (![D_21800]: (~r2_hidden(D_21800, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_136934])).
% 27.93/17.29  tff(c_137012, plain, (![B_21801]: (r1_tarski('#skF_6', B_21801))), inference(resolution, [status(thm)], [c_6, c_136965])).
% 27.93/17.29  tff(c_117452, plain, (![B_20984]: (r1_tarski(k2_relat_1(k1_xboole_0), B_20984))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_117440])).
% 27.93/17.29  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.93/17.29  tff(c_117510, plain, (![B_20984]: (k2_relat_1(k1_xboole_0)=B_20984 | ~r1_tarski(B_20984, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_117452, c_8])).
% 27.93/17.29  tff(c_136171, plain, (![B_20984]: (k2_relat_1('#skF_8')=B_20984 | ~r1_tarski(B_20984, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_136164, c_136164, c_117510])).
% 27.93/17.29  tff(c_137059, plain, (k2_relat_1('#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_137012, c_136171])).
% 27.93/17.29  tff(c_91498, plain, (![B_12012, B_12013]: (r1_tarski(k2_relat_1(B_12012), B_12013) | ~v5_relat_1(B_12012, '#skF_1'(k2_relat_1(B_12012), B_12013)) | ~v1_relat_1(B_12012))), inference(resolution, [status(thm)], [c_212, c_153])).
% 27.93/17.29  tff(c_91539, plain, (![A_10, B_12013]: (r1_tarski(k2_relat_1(A_10), B_12013) | ~v1_relat_1(A_10) | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_286, c_91498])).
% 27.93/17.29  tff(c_91448, plain, (![A_12001, D_12002]: (r2_hidden(k1_funct_1(A_12001, D_12002), k2_relat_1(A_12001)) | ~r2_hidden(D_12002, k1_relat_1(A_12001)) | ~v1_funct_1(A_12001) | ~v1_relat_1(A_12001))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.29  tff(c_103736, plain, (![A_15548, D_15549]: (~r1_tarski(k2_relat_1(A_15548), k1_funct_1(A_15548, D_15549)) | ~r2_hidden(D_15549, k1_relat_1(A_15548)) | ~v1_funct_1(A_15548) | ~v1_relat_1(A_15548))), inference(resolution, [status(thm)], [c_91448, c_52])).
% 27.93/17.29  tff(c_103763, plain, (![D_15550, A_15551]: (~r2_hidden(D_15550, k1_relat_1(A_15551)) | ~v1_funct_1(A_15551) | ~v1_relat_1(A_15551) | ~r1_tarski(A_15551, k1_xboole_0))), inference(resolution, [status(thm)], [c_91539, c_103736])).
% 27.93/17.29  tff(c_103819, plain, (![D_15550]: (~r2_hidden(D_15550, '#skF_6') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_78, c_103763])).
% 27.93/17.29  tff(c_103836, plain, (![D_15550]: (~r2_hidden(D_15550, '#skF_6') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_103819])).
% 27.93/17.29  tff(c_103837, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_103836])).
% 27.93/17.29  tff(c_92122, plain, (![A_12037, C_12038]: (r2_hidden('#skF_5'(A_12037, k2_relat_1(A_12037), C_12038), k1_relat_1(A_12037)) | ~r2_hidden(C_12038, k2_relat_1(A_12037)) | ~v1_funct_1(A_12037) | ~v1_relat_1(A_12037))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.29  tff(c_92136, plain, (![C_12038]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_12038), '#skF_6') | ~r2_hidden(C_12038, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_92122])).
% 27.93/17.29  tff(c_92279, plain, (![C_12042]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_12042), '#skF_6') | ~r2_hidden(C_12042, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_92136])).
% 27.93/17.29  tff(c_91599, plain, (![A_12015, C_12016]: (k1_funct_1(A_12015, '#skF_5'(A_12015, k2_relat_1(A_12015), C_12016))=C_12016 | ~r2_hidden(C_12016, k2_relat_1(A_12015)) | ~v1_funct_1(A_12015) | ~v1_relat_1(A_12015))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.29  tff(c_91629, plain, (![C_12016]: (r2_hidden(C_12016, '#skF_7') | ~r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_12016), '#skF_6') | ~r2_hidden(C_12016, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_91599, c_76])).
% 27.93/17.29  tff(c_91645, plain, (![C_12016]: (r2_hidden(C_12016, '#skF_7') | ~r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_12016), '#skF_6') | ~r2_hidden(C_12016, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_91629])).
% 27.93/17.29  tff(c_92291, plain, (![C_12043]: (r2_hidden(C_12043, '#skF_7') | ~r2_hidden(C_12043, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_92279, c_91645])).
% 27.93/17.29  tff(c_92314, plain, (![B_12044]: (r2_hidden('#skF_1'(k2_relat_1('#skF_8'), B_12044), '#skF_7') | r1_tarski(k2_relat_1('#skF_8'), B_12044))), inference(resolution, [status(thm)], [c_6, c_92291])).
% 27.93/17.29  tff(c_92325, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_92314, c_4])).
% 27.93/17.29  tff(c_239, plain, (![A_121]: (r1_tarski(A_121, k2_zfmisc_1(k1_relat_1(A_121), k2_relat_1(A_121))) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_69])).
% 27.93/17.29  tff(c_251, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8'))) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_78, c_239])).
% 27.93/17.29  tff(c_256, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_251])).
% 27.93/17.29  tff(c_91925, plain, (![D_12026, C_12027, B_12028, A_12029]: (m1_subset_1(D_12026, k1_zfmisc_1(k2_zfmisc_1(C_12027, B_12028))) | ~r1_tarski(k2_relat_1(D_12026), B_12028) | ~m1_subset_1(D_12026, k1_zfmisc_1(k2_zfmisc_1(C_12027, A_12029))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 27.93/17.29  tff(c_104533, plain, (![A_15573, C_15574, B_15575, A_15576]: (m1_subset_1(A_15573, k1_zfmisc_1(k2_zfmisc_1(C_15574, B_15575))) | ~r1_tarski(k2_relat_1(A_15573), B_15575) | ~r1_tarski(A_15573, k2_zfmisc_1(C_15574, A_15576)))), inference(resolution, [status(thm)], [c_22, c_91925])).
% 27.93/17.29  tff(c_104662, plain, (![B_15583]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_15583))) | ~r1_tarski(k2_relat_1('#skF_8'), B_15583))), inference(resolution, [status(thm)], [c_256, c_104533])).
% 27.93/17.29  tff(c_104673, plain, (![B_15583]: (k1_relset_1('#skF_6', B_15583, '#skF_8')=k1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), B_15583))), inference(resolution, [status(thm)], [c_104662, c_58])).
% 27.93/17.29  tff(c_104769, plain, (![B_15586]: (k1_relset_1('#skF_6', B_15586, '#skF_8')='#skF_6' | ~r1_tarski(k2_relat_1('#skF_8'), B_15586))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_104673])).
% 27.93/17.29  tff(c_104796, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_92325, c_104769])).
% 27.93/17.29  tff(c_104851, plain, (![B_15589]: (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', B_15589)) | ~r1_tarski(k2_relat_1('#skF_8'), B_15589))), inference(resolution, [status(thm)], [c_104662, c_20])).
% 27.93/17.29  tff(c_104878, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_92325, c_104851])).
% 27.93/17.29  tff(c_102648, plain, (![B_15477, C_15478, A_15479]: (k1_xboole_0=B_15477 | v1_funct_2(C_15478, A_15479, B_15477) | k1_relset_1(A_15479, B_15477, C_15478)!=A_15479 | ~m1_subset_1(C_15478, k1_zfmisc_1(k2_zfmisc_1(A_15479, B_15477))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 27.93/17.29  tff(c_105132, plain, (![B_15601, A_15602, A_15603]: (k1_xboole_0=B_15601 | v1_funct_2(A_15602, A_15603, B_15601) | k1_relset_1(A_15603, B_15601, A_15602)!=A_15603 | ~r1_tarski(A_15602, k2_zfmisc_1(A_15603, B_15601)))), inference(resolution, [status(thm)], [c_22, c_102648])).
% 27.93/17.29  tff(c_105138, plain, (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', '#skF_6', '#skF_7') | k1_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_6'), inference(resolution, [status(thm)], [c_104878, c_105132])).
% 27.93/17.29  tff(c_105182, plain, (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_104796, c_105138])).
% 27.93/17.29  tff(c_105183, plain, (k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_167, c_105182])).
% 27.93/17.29  tff(c_104686, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_104662])).
% 27.93/17.29  tff(c_104734, plain, (~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_104686])).
% 27.93/17.29  tff(c_105204, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_105183, c_104734])).
% 27.93/17.29  tff(c_105294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92325, c_105204])).
% 27.93/17.29  tff(c_105295, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_104686])).
% 27.93/17.29  tff(c_105309, plain, (r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_105295, c_20])).
% 27.93/17.29  tff(c_105320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103837, c_105309])).
% 27.93/17.29  tff(c_105321, plain, (![D_15550]: (~r2_hidden(D_15550, '#skF_6'))), inference(splitRight, [status(thm)], [c_103836])).
% 27.93/17.29  tff(c_289, plain, (![A_130, B_131, A_132]: (v5_relat_1(A_130, B_131) | ~r1_tarski(A_130, k2_zfmisc_1(A_132, B_131)))), inference(resolution, [status(thm)], [c_22, c_264])).
% 27.93/17.29  tff(c_321, plain, (![A_136, B_137]: (v5_relat_1(k2_zfmisc_1(A_136, B_137), B_137))), inference(resolution, [status(thm)], [c_12, c_289])).
% 27.93/17.29  tff(c_324, plain, (![B_9]: (v5_relat_1(k1_xboole_0, B_9))), inference(superposition, [status(thm), theory('equality')], [c_18, c_321])).
% 27.93/17.29  tff(c_91522, plain, (![B_12013]: (r1_tarski(k2_relat_1(k1_xboole_0), B_12013) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_324, c_91498])).
% 27.93/17.29  tff(c_91538, plain, (![B_12013]: (r1_tarski(k2_relat_1(k1_xboole_0), B_12013))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_91522])).
% 27.93/17.29  tff(c_100431, plain, (![A_15388, D_15389]: (~r1_tarski(k2_relat_1(A_15388), k1_funct_1(A_15388, D_15389)) | ~r2_hidden(D_15389, k1_relat_1(A_15388)) | ~v1_funct_1(A_15388) | ~v1_relat_1(A_15388))), inference(resolution, [status(thm)], [c_91448, c_52])).
% 27.93/17.29  tff(c_100608, plain, (![D_15398, A_15399]: (~r2_hidden(D_15398, k1_relat_1(A_15399)) | ~v1_funct_1(A_15399) | ~v1_relat_1(A_15399) | ~r1_tarski(A_15399, k1_xboole_0))), inference(resolution, [status(thm)], [c_91539, c_100431])).
% 27.93/17.29  tff(c_100668, plain, (![D_15398]: (~r2_hidden(D_15398, '#skF_6') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_78, c_100608])).
% 27.93/17.29  tff(c_100686, plain, (![D_15398]: (~r2_hidden(D_15398, '#skF_6') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_100668])).
% 27.93/17.29  tff(c_100687, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_100686])).
% 27.93/17.29  tff(c_92331, plain, (v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_92325, c_24])).
% 27.93/17.29  tff(c_92337, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_92331])).
% 27.93/17.29  tff(c_101273, plain, (![A_15425, C_15426, B_15427, A_15428]: (m1_subset_1(A_15425, k1_zfmisc_1(k2_zfmisc_1(C_15426, B_15427))) | ~r1_tarski(k2_relat_1(A_15425), B_15427) | ~r1_tarski(A_15425, k2_zfmisc_1(C_15426, A_15428)))), inference(resolution, [status(thm)], [c_22, c_91925])).
% 27.93/17.29  tff(c_101427, plain, (![B_15433]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_15433))) | ~r1_tarski(k2_relat_1('#skF_8'), B_15433))), inference(resolution, [status(thm)], [c_256, c_101273])).
% 27.93/17.29  tff(c_101438, plain, (![B_15433]: (k1_relset_1('#skF_6', B_15433, '#skF_8')=k1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), B_15433))), inference(resolution, [status(thm)], [c_101427, c_58])).
% 27.93/17.29  tff(c_101581, plain, (![B_15440]: (k1_relset_1('#skF_6', B_15440, '#skF_8')='#skF_6' | ~r1_tarski(k2_relat_1('#skF_8'), B_15440))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_101438])).
% 27.93/17.29  tff(c_101605, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_92325, c_101581])).
% 27.93/17.29  tff(c_101665, plain, (![B_15443]: (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', B_15443)) | ~r1_tarski(k2_relat_1('#skF_8'), B_15443))), inference(resolution, [status(thm)], [c_101427, c_20])).
% 27.93/17.29  tff(c_101689, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_92325, c_101665])).
% 27.93/17.29  tff(c_92551, plain, (![B_12061, C_12062, A_12063]: (k1_xboole_0=B_12061 | v1_funct_2(C_12062, A_12063, B_12061) | k1_relset_1(A_12063, B_12061, C_12062)!=A_12063 | ~m1_subset_1(C_12062, k1_zfmisc_1(k2_zfmisc_1(A_12063, B_12061))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 27.93/17.29  tff(c_102131, plain, (![B_15462, A_15463, A_15464]: (k1_xboole_0=B_15462 | v1_funct_2(A_15463, A_15464, B_15462) | k1_relset_1(A_15464, B_15462, A_15463)!=A_15464 | ~r1_tarski(A_15463, k2_zfmisc_1(A_15464, B_15462)))), inference(resolution, [status(thm)], [c_22, c_92551])).
% 27.93/17.29  tff(c_102143, plain, (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', '#skF_6', '#skF_7') | k1_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_6'), inference(resolution, [status(thm)], [c_101689, c_102131])).
% 27.93/17.29  tff(c_102192, plain, (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_101605, c_102143])).
% 27.93/17.29  tff(c_102193, plain, (k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_167, c_102192])).
% 27.93/17.29  tff(c_101451, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_101427])).
% 27.93/17.29  tff(c_101497, plain, (~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_101451])).
% 27.93/17.29  tff(c_101506, plain, (~v5_relat_1('#skF_8', k1_xboole_0) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_26, c_101497])).
% 27.93/17.29  tff(c_101513, plain, (~v5_relat_1('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_101506])).
% 27.93/17.29  tff(c_102221, plain, (~v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_102193, c_101513])).
% 27.93/17.29  tff(c_102305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92337, c_102221])).
% 27.93/17.29  tff(c_102306, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_101451])).
% 27.93/17.29  tff(c_102320, plain, (r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_102306, c_20])).
% 27.93/17.29  tff(c_102331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100687, c_102320])).
% 27.93/17.29  tff(c_102332, plain, (![D_15398]: (~r2_hidden(D_15398, '#skF_6'))), inference(splitRight, [status(thm)], [c_100686])).
% 27.93/17.29  tff(c_92652, plain, (![A_12073, B_12074]: (r2_hidden('#skF_3'(A_12073, B_12074), k1_relat_1(A_12073)) | r2_hidden('#skF_4'(A_12073, B_12074), B_12074) | k2_relat_1(A_12073)=B_12074 | ~v1_funct_1(A_12073) | ~v1_relat_1(A_12073))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.29  tff(c_92676, plain, (![B_12074]: (r2_hidden('#skF_3'('#skF_8', B_12074), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_12074), B_12074) | k2_relat_1('#skF_8')=B_12074 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_92652])).
% 27.93/17.29  tff(c_92689, plain, (![B_12075]: (r2_hidden('#skF_3'('#skF_8', B_12075), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_12075), B_12075) | k2_relat_1('#skF_8')=B_12075)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_92676])).
% 27.93/17.29  tff(c_92758, plain, (![B_12077]: (~r1_tarski(B_12077, '#skF_4'('#skF_8', B_12077)) | r2_hidden('#skF_3'('#skF_8', B_12077), '#skF_6') | k2_relat_1('#skF_8')=B_12077)), inference(resolution, [status(thm)], [c_92689, c_52])).
% 27.93/17.29  tff(c_92769, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1(k1_xboole_0)), '#skF_6') | k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_91538, c_92758])).
% 27.93/17.29  tff(c_92820, plain, (k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_92769])).
% 27.93/17.29  tff(c_92831, plain, (![B_12013]: (r1_tarski(k2_relat_1('#skF_8'), B_12013))), inference(demodulation, [status(thm), theory('equality')], [c_92820, c_91538])).
% 27.93/17.29  tff(c_93702, plain, (![A_12115, D_12116]: (~r1_tarski(k2_relat_1(A_12115), k1_funct_1(A_12115, D_12116)) | ~r2_hidden(D_12116, k1_relat_1(A_12115)) | ~v1_funct_1(A_12115) | ~v1_relat_1(A_12115))), inference(resolution, [status(thm)], [c_91448, c_52])).
% 27.93/17.29  tff(c_93712, plain, (![D_12116]: (~r2_hidden(D_12116, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_92831, c_93702])).
% 27.93/17.29  tff(c_93745, plain, (![D_12117]: (~r2_hidden(D_12117, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_93712])).
% 27.93/17.29  tff(c_93783, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_93745])).
% 27.93/17.29  tff(c_93792, plain, (![B_12118]: (r1_tarski('#skF_6', B_12118))), inference(resolution, [status(thm)], [c_6, c_93745])).
% 27.93/17.29  tff(c_91540, plain, (![B_12014]: (r1_tarski(k2_relat_1(k1_xboole_0), B_12014))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_91522])).
% 27.93/17.29  tff(c_91598, plain, (![B_12014]: (k2_relat_1(k1_xboole_0)=B_12014 | ~r1_tarski(B_12014, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_91540, c_8])).
% 27.93/17.29  tff(c_92830, plain, (![B_12014]: (k2_relat_1('#skF_8')=B_12014 | ~r1_tarski(B_12014, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_92820, c_92820, c_91598])).
% 27.93/17.29  tff(c_93841, plain, (k2_relat_1('#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_93792, c_92830])).
% 27.93/17.29  tff(c_93872, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_93841, c_256])).
% 27.93/17.29  tff(c_94280, plain, (![A_12122, C_12123, B_12124, A_12125]: (m1_subset_1(A_12122, k1_zfmisc_1(k2_zfmisc_1(C_12123, B_12124))) | ~r1_tarski(k2_relat_1(A_12122), B_12124) | ~r1_tarski(A_12122, k2_zfmisc_1(C_12123, A_12125)))), inference(resolution, [status(thm)], [c_22, c_91925])).
% 27.93/17.29  tff(c_94282, plain, (![B_12124]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_12124))) | ~r1_tarski(k2_relat_1('#skF_8'), B_12124))), inference(resolution, [status(thm)], [c_93872, c_94280])).
% 27.93/17.29  tff(c_94753, plain, (![B_12146]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_12146))))), inference(demodulation, [status(thm), theory('equality')], [c_93783, c_93841, c_94282])).
% 27.93/17.29  tff(c_94764, plain, (![B_12146]: (k1_relset_1('#skF_6', B_12146, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_94753, c_58])).
% 27.93/17.29  tff(c_94783, plain, (![B_12146]: (k1_relset_1('#skF_6', B_12146, '#skF_8')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_94764])).
% 27.93/17.29  tff(c_68, plain, (![B_74, C_75, A_73]: (k1_xboole_0=B_74 | v1_funct_2(C_75, A_73, B_74) | k1_relset_1(A_73, B_74, C_75)!=A_73 | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 27.93/17.29  tff(c_94777, plain, (![B_12146]: (k1_xboole_0=B_12146 | v1_funct_2('#skF_8', '#skF_6', B_12146) | k1_relset_1('#skF_6', B_12146, '#skF_8')!='#skF_6')), inference(resolution, [status(thm)], [c_94753, c_68])).
% 27.93/17.29  tff(c_97446, plain, (![B_12258]: (k1_xboole_0=B_12258 | v1_funct_2('#skF_8', '#skF_6', B_12258))), inference(demodulation, [status(thm), theory('equality')], [c_94783, c_94777])).
% 27.93/17.29  tff(c_97458, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_97446, c_167])).
% 27.93/17.29  tff(c_94776, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_94753])).
% 27.93/17.29  tff(c_375, plain, (![A_145, B_146, C_147]: (k1_relset_1(A_145, B_146, C_147)=k1_relat_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 27.93/17.29  tff(c_382, plain, (![B_9, C_147]: (k1_relset_1(k1_xboole_0, B_9, C_147)=k1_relat_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_375])).
% 27.93/17.29  tff(c_94794, plain, (![B_9]: (k1_relset_1(k1_xboole_0, B_9, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_94776, c_382])).
% 27.93/17.29  tff(c_94806, plain, (![B_9]: (k1_relset_1(k1_xboole_0, B_9, '#skF_8')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_94794])).
% 27.93/17.29  tff(c_66, plain, (![C_75, B_74]: (v1_funct_2(C_75, k1_xboole_0, B_74) | k1_relset_1(k1_xboole_0, B_74, C_75)!=k1_xboole_0 | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_74))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 27.93/17.29  tff(c_85, plain, (![C_75, B_74]: (v1_funct_2(C_75, k1_xboole_0, B_74) | k1_relset_1(k1_xboole_0, B_74, C_75)!=k1_xboole_0 | ~m1_subset_1(C_75, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_66])).
% 27.93/17.29  tff(c_94802, plain, (![B_74]: (v1_funct_2('#skF_8', k1_xboole_0, B_74) | k1_relset_1(k1_xboole_0, B_74, '#skF_8')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_94776, c_85])).
% 27.93/17.29  tff(c_95514, plain, (![B_74]: (v1_funct_2('#skF_8', k1_xboole_0, B_74) | k1_xboole_0!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_94806, c_94802])).
% 27.93/17.29  tff(c_95515, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_95514])).
% 27.93/17.29  tff(c_97471, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_97458, c_95515])).
% 27.93/17.29  tff(c_97818, plain, (![A_12267]: (k2_zfmisc_1(A_12267, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_97458, c_97458, c_16])).
% 27.93/17.29  tff(c_28, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 27.93/17.29  tff(c_313, plain, (![A_132, B_131]: (v5_relat_1(k2_zfmisc_1(A_132, B_131), B_131))), inference(resolution, [status(thm)], [c_12, c_289])).
% 27.93/17.29  tff(c_229, plain, (![B_116, A_117]: (k2_relat_1(B_116)=A_117 | ~r1_tarski(A_117, k2_relat_1(B_116)) | ~v5_relat_1(B_116, A_117) | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_212, c_8])).
% 27.93/17.29  tff(c_92071, plain, (![B_12036]: (k2_relat_1(k1_xboole_0)=k2_relat_1(B_12036) | ~v5_relat_1(B_12036, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(B_12036))), inference(resolution, [status(thm)], [c_91540, c_229])).
% 27.93/17.29  tff(c_92095, plain, (![A_132]: (k2_relat_1(k2_zfmisc_1(A_132, k2_relat_1(k1_xboole_0)))=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1(A_132, k2_relat_1(k1_xboole_0))))), inference(resolution, [status(thm)], [c_313, c_92071])).
% 27.93/17.29  tff(c_92116, plain, (![A_132]: (k2_relat_1(k2_zfmisc_1(A_132, k2_relat_1(k1_xboole_0)))=k2_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_92095])).
% 27.93/17.29  tff(c_92823, plain, (![A_132]: (k2_relat_1(k2_zfmisc_1(A_132, k2_relat_1('#skF_8')))=k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_92820, c_92820, c_92116])).
% 27.93/17.29  tff(c_93856, plain, (![A_132]: (k2_relat_1(k2_zfmisc_1(A_132, '#skF_6'))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_93841, c_93841, c_92823])).
% 27.93/17.29  tff(c_94317, plain, (![A_12126]: (k2_relat_1(k2_zfmisc_1(A_12126, '#skF_6'))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_93841, c_93841, c_92823])).
% 27.93/17.29  tff(c_94374, plain, (![A_12126]: (r1_tarski(k2_zfmisc_1(A_12126, '#skF_6'), k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_12126, '#skF_6')), '#skF_6')) | ~v1_relat_1(k2_zfmisc_1(A_12126, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_94317, c_32])).
% 27.93/17.29  tff(c_95717, plain, (![A_12201]: (r1_tarski(k2_zfmisc_1(A_12201, '#skF_6'), k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_12201, '#skF_6')), '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_94374])).
% 27.93/17.29  tff(c_91933, plain, (![A_10, C_12027, B_12028, A_12029]: (m1_subset_1(A_10, k1_zfmisc_1(k2_zfmisc_1(C_12027, B_12028))) | ~r1_tarski(k2_relat_1(A_10), B_12028) | ~r1_tarski(A_10, k2_zfmisc_1(C_12027, A_12029)))), inference(resolution, [status(thm)], [c_22, c_91925])).
% 27.93/17.29  tff(c_95725, plain, (![A_12201, B_12028]: (m1_subset_1(k2_zfmisc_1(A_12201, '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_12201, '#skF_6')), B_12028))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(A_12201, '#skF_6')), B_12028))), inference(resolution, [status(thm)], [c_95717, c_91933])).
% 27.93/17.29  tff(c_96968, plain, (![A_12239, B_12240]: (m1_subset_1(k2_zfmisc_1(A_12239, '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_12239, '#skF_6')), B_12240))))), inference(demodulation, [status(thm), theory('equality')], [c_93783, c_93856, c_95725])).
% 27.93/17.29  tff(c_97010, plain, (![A_12239, B_12240]: (r1_tarski(k2_zfmisc_1(A_12239, '#skF_6'), k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_12239, '#skF_6')), B_12240)))), inference(resolution, [status(thm)], [c_96968, c_20])).
% 27.93/17.29  tff(c_97823, plain, (![A_12239]: (r1_tarski(k2_zfmisc_1(A_12239, '#skF_6'), '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_97818, c_97010])).
% 27.93/17.29  tff(c_62, plain, (![A_73]: (v1_funct_2(k1_xboole_0, A_73, k1_xboole_0) | k1_xboole_0=A_73 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_73, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 27.93/17.29  tff(c_88, plain, (![A_73]: (v1_funct_2(k1_xboole_0, A_73, k1_xboole_0) | k1_xboole_0=A_73 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_62])).
% 27.93/17.29  tff(c_338, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_88])).
% 27.93/17.29  tff(c_341, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_338])).
% 27.93/17.29  tff(c_345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_341])).
% 27.93/17.29  tff(c_347, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_88])).
% 27.93/17.29  tff(c_97510, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_97458, c_97458, c_347])).
% 27.93/17.29  tff(c_93866, plain, (k2_relat_1(k1_xboole_0)='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_93841, c_92820])).
% 27.93/17.29  tff(c_97484, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_97458, c_93866])).
% 27.93/17.29  tff(c_93612, plain, (![D_12108, A_12109, B_12110]: (m1_subset_1(D_12108, k1_zfmisc_1(k2_zfmisc_1(A_12109, B_12110))) | ~r1_tarski(k2_relat_1(D_12108), B_12110) | ~m1_subset_1(D_12108, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_91925])).
% 27.93/17.29  tff(c_93645, plain, (![D_12108, A_12109, B_12110]: (r1_tarski(D_12108, k2_zfmisc_1(A_12109, B_12110)) | ~r1_tarski(k2_relat_1(D_12108), B_12110) | ~m1_subset_1(D_12108, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_93612, c_20])).
% 27.93/17.29  tff(c_98401, plain, (![D_12308, A_12309, B_12310]: (r1_tarski(D_12308, k2_zfmisc_1(A_12309, B_12310)) | ~r1_tarski(k2_relat_1(D_12308), B_12310) | ~m1_subset_1(D_12308, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_97458, c_93645])).
% 27.93/17.29  tff(c_98403, plain, (![A_12309, B_12310]: (r1_tarski('#skF_7', k2_zfmisc_1(A_12309, B_12310)) | ~r1_tarski('#skF_6', B_12310) | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_97484, c_98401])).
% 27.93/17.29  tff(c_98432, plain, (![A_12311, B_12312]: (r1_tarski('#skF_7', k2_zfmisc_1(A_12311, B_12312)))), inference(demodulation, [status(thm), theory('equality')], [c_97510, c_93783, c_98403])).
% 27.93/17.29  tff(c_99126, plain, (![A_12350, B_12351]: (k2_zfmisc_1(A_12350, B_12351)='#skF_7' | ~r1_tarski(k2_zfmisc_1(A_12350, B_12351), '#skF_7'))), inference(resolution, [status(thm)], [c_98432, c_8])).
% 27.93/17.29  tff(c_99169, plain, (![A_12352]: (k2_zfmisc_1(A_12352, '#skF_6')='#skF_7')), inference(resolution, [status(thm)], [c_97823, c_99126])).
% 27.93/17.29  tff(c_14, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.93/17.29  tff(c_97517, plain, (![B_9, A_8]: (B_9='#skF_7' | A_8='#skF_7' | k2_zfmisc_1(A_8, B_9)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_97458, c_97458, c_97458, c_14])).
% 27.93/17.29  tff(c_99188, plain, (![A_12352]: ('#skF_7'='#skF_6' | A_12352='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_99169, c_97517])).
% 27.93/17.29  tff(c_99282, plain, (![A_12353]: (A_12353='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_97471, c_99188])).
% 27.93/17.29  tff(c_97481, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_97458, c_94776])).
% 27.93/17.29  tff(c_98411, plain, (![A_12309, B_12310]: (r1_tarski('#skF_8', k2_zfmisc_1(A_12309, B_12310)) | ~r1_tarski('#skF_6', B_12310) | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_93841, c_98401])).
% 27.93/17.29  tff(c_98463, plain, (![A_12313, B_12314]: (r1_tarski('#skF_8', k2_zfmisc_1(A_12313, B_12314)))), inference(demodulation, [status(thm), theory('equality')], [c_97481, c_93783, c_98411])).
% 27.93/17.29  tff(c_386, plain, (![A_145, B_146, A_10]: (k1_relset_1(A_145, B_146, A_10)=k1_relat_1(A_10) | ~r1_tarski(A_10, k2_zfmisc_1(A_145, B_146)))), inference(resolution, [status(thm)], [c_22, c_375])).
% 27.93/17.29  tff(c_98468, plain, (![A_12313, B_12314]: (k1_relset_1(A_12313, B_12314, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_98463, c_386])).
% 27.93/17.29  tff(c_98485, plain, (![A_12313, B_12314]: (k1_relset_1(A_12313, B_12314, '#skF_8')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_98468])).
% 27.93/17.29  tff(c_99322, plain, ('#skF_7'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_99282, c_98485])).
% 27.93/17.29  tff(c_99731, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97471, c_99322])).
% 27.93/17.29  tff(c_99733, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_95514])).
% 27.93/17.29  tff(c_94810, plain, (r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_94776, c_20])).
% 27.93/17.29  tff(c_94825, plain, (k1_xboole_0='#skF_8' | ~r1_tarski(k1_xboole_0, '#skF_8')), inference(resolution, [status(thm)], [c_94810, c_8])).
% 27.93/17.29  tff(c_94937, plain, (~r1_tarski(k1_xboole_0, '#skF_8')), inference(splitLeft, [status(thm)], [c_94825])).
% 27.93/17.29  tff(c_99738, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_99733, c_94937])).
% 27.93/17.29  tff(c_99785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93783, c_99738])).
% 27.93/17.29  tff(c_99786, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_94825])).
% 27.93/17.29  tff(c_68914, plain, (![B_10985, B_10986]: (r1_tarski(k2_relat_1(B_10985), B_10986) | ~v5_relat_1(B_10985, '#skF_1'(k2_relat_1(B_10985), B_10986)) | ~v1_relat_1(B_10985))), inference(resolution, [status(thm)], [c_212, c_153])).
% 27.93/17.29  tff(c_68938, plain, (![B_10986]: (r1_tarski(k2_relat_1(k1_xboole_0), B_10986) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_324, c_68914])).
% 27.93/17.29  tff(c_68954, plain, (![B_10986]: (r1_tarski(k2_relat_1(k1_xboole_0), B_10986))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_68938])).
% 27.93/17.29  tff(c_68955, plain, (![A_10, B_10986]: (r1_tarski(k2_relat_1(A_10), B_10986) | ~v1_relat_1(A_10) | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_286, c_68914])).
% 27.93/17.29  tff(c_68903, plain, (![A_10983, D_10984]: (r2_hidden(k1_funct_1(A_10983, D_10984), k2_relat_1(A_10983)) | ~r2_hidden(D_10984, k1_relat_1(A_10983)) | ~v1_funct_1(A_10983) | ~v1_relat_1(A_10983))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.29  tff(c_79136, plain, (![A_11417, D_11418]: (~r1_tarski(k2_relat_1(A_11417), k1_funct_1(A_11417, D_11418)) | ~r2_hidden(D_11418, k1_relat_1(A_11417)) | ~v1_funct_1(A_11417) | ~v1_relat_1(A_11417))), inference(resolution, [status(thm)], [c_68903, c_52])).
% 27.93/17.29  tff(c_79183, plain, (![D_11419, A_11420]: (~r2_hidden(D_11419, k1_relat_1(A_11420)) | ~v1_funct_1(A_11420) | ~v1_relat_1(A_11420) | ~r1_tarski(A_11420, k1_xboole_0))), inference(resolution, [status(thm)], [c_68955, c_79136])).
% 27.93/17.29  tff(c_79244, plain, (![D_11419]: (~r2_hidden(D_11419, '#skF_6') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_78, c_79183])).
% 27.93/17.29  tff(c_79261, plain, (![D_11419]: (~r2_hidden(D_11419, '#skF_6') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_79244])).
% 27.93/17.29  tff(c_79262, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_79261])).
% 27.93/17.29  tff(c_69466, plain, (![A_11005, C_11006]: (r2_hidden('#skF_5'(A_11005, k2_relat_1(A_11005), C_11006), k1_relat_1(A_11005)) | ~r2_hidden(C_11006, k2_relat_1(A_11005)) | ~v1_funct_1(A_11005) | ~v1_relat_1(A_11005))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.29  tff(c_69477, plain, (![C_11006]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_11006), '#skF_6') | ~r2_hidden(C_11006, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_69466])).
% 27.93/17.29  tff(c_69487, plain, (![C_11007]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_11007), '#skF_6') | ~r2_hidden(C_11007, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_69477])).
% 27.93/17.29  tff(c_69261, plain, (![A_10993, C_10994]: (k1_funct_1(A_10993, '#skF_5'(A_10993, k2_relat_1(A_10993), C_10994))=C_10994 | ~r2_hidden(C_10994, k2_relat_1(A_10993)) | ~v1_funct_1(A_10993) | ~v1_relat_1(A_10993))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.29  tff(c_69291, plain, (![C_10994]: (r2_hidden(C_10994, '#skF_7') | ~r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_10994), '#skF_6') | ~r2_hidden(C_10994, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_69261, c_76])).
% 27.93/17.29  tff(c_69310, plain, (![C_10994]: (r2_hidden(C_10994, '#skF_7') | ~r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_10994), '#skF_6') | ~r2_hidden(C_10994, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_69291])).
% 27.93/17.29  tff(c_69499, plain, (![C_11008]: (r2_hidden(C_11008, '#skF_7') | ~r2_hidden(C_11008, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_69487, c_69310])).
% 27.93/17.29  tff(c_69522, plain, (![B_11009]: (r2_hidden('#skF_1'(k2_relat_1('#skF_8'), B_11009), '#skF_7') | r1_tarski(k2_relat_1('#skF_8'), B_11009))), inference(resolution, [status(thm)], [c_6, c_69499])).
% 27.93/17.29  tff(c_69533, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_69522, c_4])).
% 27.93/17.29  tff(c_69539, plain, (v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_69533, c_24])).
% 27.93/17.29  tff(c_69545, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_69539])).
% 27.93/17.29  tff(c_69553, plain, (![D_11010, C_11011, B_11012, A_11013]: (m1_subset_1(D_11010, k1_zfmisc_1(k2_zfmisc_1(C_11011, B_11012))) | ~r1_tarski(k2_relat_1(D_11010), B_11012) | ~m1_subset_1(D_11010, k1_zfmisc_1(k2_zfmisc_1(C_11011, A_11013))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 27.93/17.29  tff(c_79813, plain, (![A_11446, C_11447, B_11448, A_11449]: (m1_subset_1(A_11446, k1_zfmisc_1(k2_zfmisc_1(C_11447, B_11448))) | ~r1_tarski(k2_relat_1(A_11446), B_11448) | ~r1_tarski(A_11446, k2_zfmisc_1(C_11447, A_11449)))), inference(resolution, [status(thm)], [c_22, c_69553])).
% 27.93/17.29  tff(c_79967, plain, (![B_11454]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_11454))) | ~r1_tarski(k2_relat_1('#skF_8'), B_11454))), inference(resolution, [status(thm)], [c_256, c_79813])).
% 27.93/17.29  tff(c_79978, plain, (![B_11454]: (k1_relset_1('#skF_6', B_11454, '#skF_8')=k1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), B_11454))), inference(resolution, [status(thm)], [c_79967, c_58])).
% 27.93/17.29  tff(c_80078, plain, (![B_11457]: (k1_relset_1('#skF_6', B_11457, '#skF_8')='#skF_6' | ~r1_tarski(k2_relat_1('#skF_8'), B_11457))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_79978])).
% 27.93/17.29  tff(c_80102, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_69533, c_80078])).
% 27.93/17.29  tff(c_80162, plain, (![B_11460]: (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', B_11460)) | ~r1_tarski(k2_relat_1('#skF_8'), B_11460))), inference(resolution, [status(thm)], [c_79967, c_20])).
% 27.93/17.29  tff(c_80186, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_69533, c_80162])).
% 27.93/17.29  tff(c_69845, plain, (![B_11027, C_11028, A_11029]: (k1_xboole_0=B_11027 | v1_funct_2(C_11028, A_11029, B_11027) | k1_relset_1(A_11029, B_11027, C_11028)!=A_11029 | ~m1_subset_1(C_11028, k1_zfmisc_1(k2_zfmisc_1(A_11029, B_11027))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 27.93/17.29  tff(c_80875, plain, (![B_11498, A_11499, A_11500]: (k1_xboole_0=B_11498 | v1_funct_2(A_11499, A_11500, B_11498) | k1_relset_1(A_11500, B_11498, A_11499)!=A_11500 | ~r1_tarski(A_11499, k2_zfmisc_1(A_11500, B_11498)))), inference(resolution, [status(thm)], [c_22, c_69845])).
% 27.93/17.29  tff(c_80887, plain, (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', '#skF_6', '#skF_7') | k1_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_6'), inference(resolution, [status(thm)], [c_80186, c_80875])).
% 27.93/17.29  tff(c_80936, plain, (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_80102, c_80887])).
% 27.93/17.29  tff(c_80937, plain, (k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_167, c_80936])).
% 27.93/17.29  tff(c_79991, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_79967])).
% 27.93/17.29  tff(c_80037, plain, (~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_79991])).
% 27.93/17.29  tff(c_80046, plain, (~v5_relat_1('#skF_8', k1_xboole_0) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_26, c_80037])).
% 27.93/17.29  tff(c_80053, plain, (~v5_relat_1('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80046])).
% 27.93/17.29  tff(c_80969, plain, (~v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_80937, c_80053])).
% 27.93/17.29  tff(c_81054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69545, c_80969])).
% 27.93/17.29  tff(c_81055, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_79991])).
% 27.93/17.29  tff(c_81069, plain, (r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_81055, c_20])).
% 27.93/17.29  tff(c_81080, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79262, c_81069])).
% 27.93/17.29  tff(c_81081, plain, (![D_11419]: (~r2_hidden(D_11419, '#skF_6'))), inference(splitRight, [status(thm)], [c_79261])).
% 27.93/17.29  tff(c_70089, plain, (![A_11047, B_11048]: (r2_hidden('#skF_3'(A_11047, B_11048), k1_relat_1(A_11047)) | r2_hidden('#skF_4'(A_11047, B_11048), B_11048) | k2_relat_1(A_11047)=B_11048 | ~v1_funct_1(A_11047) | ~v1_relat_1(A_11047))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.29  tff(c_70110, plain, (![B_11048]: (r2_hidden('#skF_3'('#skF_8', B_11048), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_11048), B_11048) | k2_relat_1('#skF_8')=B_11048 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_70089])).
% 27.93/17.29  tff(c_70119, plain, (![B_11049]: (r2_hidden('#skF_3'('#skF_8', B_11049), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_11049), B_11049) | k2_relat_1('#skF_8')=B_11049)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_70110])).
% 27.93/17.29  tff(c_70182, plain, (![B_11051]: (~r1_tarski(B_11051, '#skF_4'('#skF_8', B_11051)) | r2_hidden('#skF_3'('#skF_8', B_11051), '#skF_6') | k2_relat_1('#skF_8')=B_11051)), inference(resolution, [status(thm)], [c_70119, c_52])).
% 27.93/17.29  tff(c_70193, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1(k1_xboole_0)), '#skF_6') | k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68954, c_70182])).
% 27.93/17.29  tff(c_70195, plain, (k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_70193])).
% 27.93/17.29  tff(c_70206, plain, (![B_10986]: (r1_tarski(k2_relat_1('#skF_8'), B_10986))), inference(demodulation, [status(thm), theory('equality')], [c_70195, c_68954])).
% 27.93/17.29  tff(c_74043, plain, (![A_11180, D_11181]: (~r1_tarski(k2_relat_1(A_11180), k1_funct_1(A_11180, D_11181)) | ~r2_hidden(D_11181, k1_relat_1(A_11180)) | ~v1_funct_1(A_11180) | ~v1_relat_1(A_11180))), inference(resolution, [status(thm)], [c_68903, c_52])).
% 27.93/17.29  tff(c_74053, plain, (![D_11181]: (~r2_hidden(D_11181, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_70206, c_74043])).
% 27.93/17.29  tff(c_74133, plain, (![D_11184]: (~r2_hidden(D_11184, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_74053])).
% 27.93/17.29  tff(c_74171, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_74133])).
% 27.93/17.29  tff(c_72624, plain, (![A_11132, D_11133]: (~r1_tarski(k2_relat_1(A_11132), k1_funct_1(A_11132, D_11133)) | ~r2_hidden(D_11133, k1_relat_1(A_11132)) | ~v1_funct_1(A_11132) | ~v1_relat_1(A_11132))), inference(resolution, [status(thm)], [c_68903, c_52])).
% 27.93/17.30  tff(c_72637, plain, (![D_11133]: (~r2_hidden(D_11133, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_70206, c_72624])).
% 27.93/17.30  tff(c_72667, plain, (![D_11134]: (~r2_hidden(D_11134, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_72637])).
% 27.93/17.30  tff(c_72705, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_72667])).
% 27.93/17.30  tff(c_72714, plain, (![B_11135]: (r1_tarski('#skF_6', B_11135))), inference(resolution, [status(thm)], [c_6, c_72667])).
% 27.93/17.30  tff(c_68956, plain, (![B_10987]: (r1_tarski(k2_relat_1(k1_xboole_0), B_10987))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_68938])).
% 27.93/17.30  tff(c_69014, plain, (![B_10987]: (k2_relat_1(k1_xboole_0)=B_10987 | ~r1_tarski(B_10987, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_68956, c_8])).
% 27.93/17.30  tff(c_70205, plain, (![B_10987]: (k2_relat_1('#skF_8')=B_10987 | ~r1_tarski(B_10987, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_70195, c_70195, c_69014])).
% 27.93/17.30  tff(c_72763, plain, (k2_relat_1('#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_72714, c_70205])).
% 27.93/17.30  tff(c_72794, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_72763, c_256])).
% 27.93/17.30  tff(c_73513, plain, (![A_11153, C_11154, B_11155, A_11156]: (m1_subset_1(A_11153, k1_zfmisc_1(k2_zfmisc_1(C_11154, B_11155))) | ~r1_tarski(k2_relat_1(A_11153), B_11155) | ~r1_tarski(A_11153, k2_zfmisc_1(C_11154, A_11156)))), inference(resolution, [status(thm)], [c_22, c_69553])).
% 27.93/17.30  tff(c_73515, plain, (![B_11155]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_11155))) | ~r1_tarski(k2_relat_1('#skF_8'), B_11155))), inference(resolution, [status(thm)], [c_72794, c_73513])).
% 27.93/17.30  tff(c_73696, plain, (![B_11165]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_11165))))), inference(demodulation, [status(thm), theory('equality')], [c_72705, c_72763, c_73515])).
% 27.93/17.30  tff(c_73707, plain, (![B_11165]: (k1_relset_1('#skF_6', B_11165, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_73696, c_58])).
% 27.93/17.30  tff(c_73726, plain, (![B_11165]: (k1_relset_1('#skF_6', B_11165, '#skF_8')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_73707])).
% 27.93/17.30  tff(c_73731, plain, (![B_11165]: (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', B_11165)))), inference(resolution, [status(thm)], [c_73696, c_20])).
% 27.93/17.30  tff(c_73836, plain, (![B_11171, A_11172, A_11173]: (k1_xboole_0=B_11171 | v1_funct_2(A_11172, A_11173, B_11171) | k1_relset_1(A_11173, B_11171, A_11172)!=A_11173 | ~r1_tarski(A_11172, k2_zfmisc_1(A_11173, B_11171)))), inference(resolution, [status(thm)], [c_22, c_69845])).
% 27.93/17.30  tff(c_73839, plain, (![B_11165]: (k1_xboole_0=B_11165 | v1_funct_2('#skF_8', '#skF_6', B_11165) | k1_relset_1('#skF_6', B_11165, '#skF_8')!='#skF_6')), inference(resolution, [status(thm)], [c_73731, c_73836])).
% 27.93/17.30  tff(c_73976, plain, (![B_11179]: (k1_xboole_0=B_11179 | v1_funct_2('#skF_8', '#skF_6', B_11179))), inference(demodulation, [status(thm), theory('equality')], [c_73726, c_73839])).
% 27.93/17.30  tff(c_73987, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_73976, c_167])).
% 27.93/17.30  tff(c_71027, plain, (![A_11081, D_11082]: (~r1_tarski(k2_relat_1(A_11081), k1_funct_1(A_11081, D_11082)) | ~r2_hidden(D_11082, k1_relat_1(A_11081)) | ~v1_funct_1(A_11081) | ~v1_relat_1(A_11081))), inference(resolution, [status(thm)], [c_68903, c_52])).
% 27.93/17.30  tff(c_71040, plain, (![D_11082]: (~r2_hidden(D_11082, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_70206, c_71027])).
% 27.93/17.30  tff(c_71070, plain, (![D_11083]: (~r2_hidden(D_11083, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_71040])).
% 27.93/17.30  tff(c_71108, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_71070])).
% 27.93/17.30  tff(c_71117, plain, (![B_11084]: (r1_tarski('#skF_6', B_11084))), inference(resolution, [status(thm)], [c_6, c_71070])).
% 27.93/17.30  tff(c_71166, plain, (k2_relat_1('#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_71117, c_70205])).
% 27.93/17.30  tff(c_71197, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_71166, c_256])).
% 27.93/17.30  tff(c_71917, plain, (![A_11102, C_11103, B_11104, A_11105]: (m1_subset_1(A_11102, k1_zfmisc_1(k2_zfmisc_1(C_11103, B_11104))) | ~r1_tarski(k2_relat_1(A_11102), B_11104) | ~r1_tarski(A_11102, k2_zfmisc_1(C_11103, A_11105)))), inference(resolution, [status(thm)], [c_22, c_69553])).
% 27.93/17.30  tff(c_71921, plain, (![B_11104]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_11104))) | ~r1_tarski(k2_relat_1('#skF_8'), B_11104))), inference(resolution, [status(thm)], [c_71197, c_71917])).
% 27.93/17.30  tff(c_72043, plain, (![B_11110]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_11110))))), inference(demodulation, [status(thm), theory('equality')], [c_71108, c_71166, c_71921])).
% 27.93/17.30  tff(c_72054, plain, (![B_11110]: (k1_relset_1('#skF_6', B_11110, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_72043, c_58])).
% 27.93/17.30  tff(c_72073, plain, (![B_11110]: (k1_relset_1('#skF_6', B_11110, '#skF_8')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72054])).
% 27.93/17.30  tff(c_72078, plain, (![B_11110]: (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', B_11110)))), inference(resolution, [status(thm)], [c_72043, c_20])).
% 27.93/17.30  tff(c_72275, plain, (![B_11122, A_11123, A_11124]: (k1_xboole_0=B_11122 | v1_funct_2(A_11123, A_11124, B_11122) | k1_relset_1(A_11124, B_11122, A_11123)!=A_11124 | ~r1_tarski(A_11123, k2_zfmisc_1(A_11124, B_11122)))), inference(resolution, [status(thm)], [c_22, c_69845])).
% 27.93/17.30  tff(c_72278, plain, (![B_11110]: (k1_xboole_0=B_11110 | v1_funct_2('#skF_8', '#skF_6', B_11110) | k1_relset_1('#skF_6', B_11110, '#skF_8')!='#skF_6')), inference(resolution, [status(thm)], [c_72078, c_72275])).
% 27.93/17.30  tff(c_72319, plain, (![B_11125]: (k1_xboole_0=B_11125 | v1_funct_2('#skF_8', '#skF_6', B_11125))), inference(demodulation, [status(thm), theory('equality')], [c_72073, c_72278])).
% 27.93/17.30  tff(c_72330, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_72319, c_167])).
% 27.93/17.30  tff(c_70257, plain, (r1_tarski(k1_xboole_0, k2_zfmisc_1(k1_relat_1(k1_xboole_0), k2_relat_1('#skF_8'))) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_70195, c_32])).
% 27.93/17.30  tff(c_70300, plain, (r1_tarski(k1_xboole_0, k2_zfmisc_1(k1_relat_1(k1_xboole_0), k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_70257])).
% 27.93/17.30  tff(c_314, plain, (![C_133, B_134, A_135]: (r2_hidden(C_133, B_134) | ~r2_hidden(C_133, A_135) | ~r1_tarski(A_135, B_134))), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.93/17.30  tff(c_330, plain, (![D_139, B_140]: (r2_hidden(k1_funct_1('#skF_8', D_139), B_140) | ~r1_tarski('#skF_7', B_140) | ~r2_hidden(D_139, '#skF_6'))), inference(resolution, [status(thm)], [c_76, c_314])).
% 27.93/17.30  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.93/17.30  tff(c_336, plain, (![D_139, B_2, B_140]: (r2_hidden(k1_funct_1('#skF_8', D_139), B_2) | ~r1_tarski(B_140, B_2) | ~r1_tarski('#skF_7', B_140) | ~r2_hidden(D_139, '#skF_6'))), inference(resolution, [status(thm)], [c_330, c_2])).
% 27.93/17.30  tff(c_70856, plain, (![D_139]: (r2_hidden(k1_funct_1('#skF_8', D_139), k2_zfmisc_1(k1_relat_1(k1_xboole_0), k2_relat_1('#skF_8'))) | ~r1_tarski('#skF_7', k1_xboole_0) | ~r2_hidden(D_139, '#skF_6'))), inference(resolution, [status(thm)], [c_70300, c_336])).
% 27.93/17.30  tff(c_70868, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_70856])).
% 27.93/17.30  tff(c_72342, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72330, c_70868])).
% 27.93/17.30  tff(c_72379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_72342])).
% 27.93/17.30  tff(c_72381, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_70856])).
% 27.93/17.30  tff(c_72395, plain, (k1_xboole_0='#skF_7' | ~r1_tarski(k1_xboole_0, '#skF_7')), inference(resolution, [status(thm)], [c_72381, c_8])).
% 27.93/17.30  tff(c_72397, plain, (~r1_tarski(k1_xboole_0, '#skF_7')), inference(splitLeft, [status(thm)], [c_72395])).
% 27.93/17.30  tff(c_74002, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_73987, c_72397])).
% 27.93/17.30  tff(c_74040, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_74002])).
% 27.93/17.30  tff(c_74041, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_72395])).
% 27.93/17.30  tff(c_387, plain, (![B_148, C_149]: (k1_relset_1(k1_xboole_0, B_148, C_149)=k1_relat_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_375])).
% 27.93/17.30  tff(c_393, plain, (![B_148]: (k1_relset_1(k1_xboole_0, B_148, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_347, c_387])).
% 27.93/17.30  tff(c_68852, plain, (![C_10972, B_10973]: (v1_funct_2(C_10972, k1_xboole_0, B_10973) | k1_relset_1(k1_xboole_0, B_10973, C_10972)!=k1_xboole_0 | ~m1_subset_1(C_10972, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_66])).
% 27.93/17.30  tff(c_68854, plain, (![B_10973]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_10973) | k1_relset_1(k1_xboole_0, B_10973, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_347, c_68852])).
% 27.93/17.30  tff(c_68859, plain, (![B_10973]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_10973) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_393, c_68854])).
% 27.93/17.30  tff(c_68861, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_68859])).
% 27.93/17.30  tff(c_74088, plain, (k1_relat_1('#skF_7')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_74041, c_74041, c_68861])).
% 27.93/17.30  tff(c_74113, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_74041, c_74041, c_16])).
% 27.93/17.30  tff(c_74180, plain, (![B_11185]: (r1_tarski('#skF_6', B_11185))), inference(resolution, [status(thm)], [c_6, c_74133])).
% 27.93/17.30  tff(c_74216, plain, (k2_relat_1('#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_74180, c_70205])).
% 27.93/17.30  tff(c_69564, plain, (![B_11015]: (k2_relat_1(k1_xboole_0)=k2_relat_1(B_11015) | ~v5_relat_1(B_11015, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(B_11015))), inference(resolution, [status(thm)], [c_68956, c_229])).
% 27.93/17.30  tff(c_69588, plain, (![A_132]: (k2_relat_1(k2_zfmisc_1(A_132, k2_relat_1(k1_xboole_0)))=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1(A_132, k2_relat_1(k1_xboole_0))))), inference(resolution, [status(thm)], [c_313, c_69564])).
% 27.93/17.30  tff(c_69616, plain, (![A_11017]: (k2_relat_1(k2_zfmisc_1(A_11017, k2_relat_1(k1_xboole_0)))=k2_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_69588])).
% 27.93/17.30  tff(c_69668, plain, (![A_11017, A_12]: (v5_relat_1(k2_zfmisc_1(A_11017, k2_relat_1(k1_xboole_0)), A_12) | ~r1_tarski(k2_relat_1(k1_xboole_0), A_12) | ~v1_relat_1(k2_zfmisc_1(A_11017, k2_relat_1(k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_69616, c_24])).
% 27.93/17.30  tff(c_69708, plain, (![A_11017, A_12]: (v5_relat_1(k2_zfmisc_1(A_11017, k2_relat_1(k1_xboole_0)), A_12))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_68954, c_69668])).
% 27.93/17.30  tff(c_70197, plain, (![A_11017, A_12]: (v5_relat_1(k2_zfmisc_1(A_11017, k2_relat_1('#skF_8')), A_12))), inference(demodulation, [status(thm), theory('equality')], [c_70195, c_69708])).
% 27.93/17.30  tff(c_74691, plain, (![A_11196, A_11197]: (v5_relat_1(k2_zfmisc_1(A_11196, '#skF_6'), A_11197))), inference(demodulation, [status(thm), theory('equality')], [c_74216, c_70197])).
% 27.93/17.30  tff(c_228, plain, (![B_116, B_95]: (r1_tarski(k2_relat_1(B_116), B_95) | ~v5_relat_1(B_116, '#skF_1'(k2_relat_1(B_116), B_95)) | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_212, c_153])).
% 27.93/17.30  tff(c_74695, plain, (![A_11196, B_95]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_11196, '#skF_6')), B_95) | ~v1_relat_1(k2_zfmisc_1(A_11196, '#skF_6')))), inference(resolution, [status(thm)], [c_74691, c_228])).
% 27.93/17.30  tff(c_74930, plain, (![A_11216, B_11217]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_11216, '#skF_6')), B_11217))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_74695])).
% 27.93/17.30  tff(c_74224, plain, (![B_11185]: (B_11185='#skF_6' | ~r1_tarski(B_11185, '#skF_6'))), inference(resolution, [status(thm)], [c_74180, c_8])).
% 27.93/17.30  tff(c_74976, plain, (![A_11216]: (k2_relat_1(k2_zfmisc_1(A_11216, '#skF_6'))='#skF_6')), inference(resolution, [status(thm)], [c_74930, c_74224])).
% 27.93/17.30  tff(c_74994, plain, (![A_11218]: (k2_relat_1(k2_zfmisc_1(A_11218, '#skF_6'))='#skF_6')), inference(resolution, [status(thm)], [c_74930, c_74224])).
% 27.93/17.30  tff(c_75034, plain, (![A_11218]: (r1_tarski(k2_zfmisc_1(A_11218, '#skF_6'), k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_11218, '#skF_6')), '#skF_6')) | ~v1_relat_1(k2_zfmisc_1(A_11218, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_74994, c_32])).
% 27.93/17.30  tff(c_76854, plain, (![A_11325]: (r1_tarski(k2_zfmisc_1(A_11325, '#skF_6'), k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_11325, '#skF_6')), '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_75034])).
% 27.93/17.30  tff(c_69561, plain, (![A_10, C_11011, B_11012, A_11013]: (m1_subset_1(A_10, k1_zfmisc_1(k2_zfmisc_1(C_11011, B_11012))) | ~r1_tarski(k2_relat_1(A_10), B_11012) | ~r1_tarski(A_10, k2_zfmisc_1(C_11011, A_11013)))), inference(resolution, [status(thm)], [c_22, c_69553])).
% 27.93/17.30  tff(c_76862, plain, (![A_11325, B_11012]: (m1_subset_1(k2_zfmisc_1(A_11325, '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_11325, '#skF_6')), B_11012))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(A_11325, '#skF_6')), B_11012))), inference(resolution, [status(thm)], [c_76854, c_69561])).
% 27.93/17.30  tff(c_78111, plain, (![A_11372, B_11373]: (m1_subset_1(k2_zfmisc_1(A_11372, '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_11372, '#skF_6')), B_11373))))), inference(demodulation, [status(thm), theory('equality')], [c_74171, c_74976, c_76862])).
% 27.93/17.30  tff(c_78148, plain, (![A_11374]: (m1_subset_1(k2_zfmisc_1(A_11374, '#skF_6'), k1_zfmisc_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_74113, c_78111])).
% 27.93/17.30  tff(c_78168, plain, (![A_11374]: (r1_tarski(k2_zfmisc_1(A_11374, '#skF_6'), '#skF_7'))), inference(resolution, [status(thm)], [c_78148, c_20])).
% 27.93/17.30  tff(c_74111, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_74041, c_119])).
% 27.93/17.30  tff(c_74079, plain, (k2_relat_1('#skF_7')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74041, c_70195])).
% 27.93/17.30  tff(c_74459, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_74216, c_74079])).
% 27.93/17.30  tff(c_74775, plain, (![A_11200]: (k2_zfmisc_1(k1_relat_1(A_11200), k2_relat_1(A_11200))=A_11200 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_11200), k2_relat_1(A_11200)), A_11200) | ~v1_relat_1(A_11200))), inference(resolution, [status(thm)], [c_239, c_8])).
% 27.93/17.30  tff(c_74778, plain, (k2_zfmisc_1(k1_relat_1('#skF_7'), k2_relat_1('#skF_7'))='#skF_7' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_7'), '#skF_6'), '#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_74459, c_74775])).
% 27.93/17.30  tff(c_74789, plain, (k2_zfmisc_1(k1_relat_1('#skF_7'), '#skF_6')='#skF_7' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_7'), '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_74111, c_74459, c_74778])).
% 27.93/17.30  tff(c_77642, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_7'), '#skF_6'), '#skF_7')), inference(splitLeft, [status(thm)], [c_74789])).
% 27.93/17.30  tff(c_78174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78168, c_77642])).
% 27.93/17.30  tff(c_78175, plain, (k2_zfmisc_1(k1_relat_1('#skF_7'), '#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_74789])).
% 27.93/17.30  tff(c_74110, plain, (![B_9, A_8]: (B_9='#skF_7' | A_8='#skF_7' | k2_zfmisc_1(A_8, B_9)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_74041, c_74041, c_74041, c_14])).
% 27.93/17.30  tff(c_78207, plain, ('#skF_7'='#skF_6' | k1_relat_1('#skF_7')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_78175, c_74110])).
% 27.93/17.30  tff(c_78284, plain, ('#skF_7'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_74088, c_78207])).
% 27.93/17.30  tff(c_69546, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_69533, c_8])).
% 27.93/17.30  tff(c_69552, plain, (~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_69546])).
% 27.93/17.30  tff(c_74236, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74216, c_69552])).
% 27.93/17.30  tff(c_78338, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78284, c_74236])).
% 27.93/17.30  tff(c_78357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74171, c_78338])).
% 27.93/17.30  tff(c_78358, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1(k1_xboole_0)), '#skF_6')), inference(splitRight, [status(thm)], [c_70193])).
% 27.93/17.30  tff(c_81088, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81081, c_78358])).
% 27.93/17.30  tff(c_81089, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_69546])).
% 27.93/17.30  tff(c_320, plain, (![D_77, B_134]: (r2_hidden(k1_funct_1('#skF_8', D_77), B_134) | ~r1_tarski('#skF_7', B_134) | ~r2_hidden(D_77, '#skF_6'))), inference(resolution, [status(thm)], [c_76, c_314])).
% 27.93/17.30  tff(c_579, plain, (![C_182, A_183, B_184]: (r2_hidden(C_182, A_183) | ~r2_hidden(C_182, k2_relat_1(B_184)) | ~v5_relat_1(B_184, A_183) | ~v1_relat_1(B_184))), inference(cnfTransformation, [status(thm)], [f_65])).
% 27.93/17.30  tff(c_645, plain, (![D_192, A_193, B_194]: (r2_hidden(k1_funct_1('#skF_8', D_192), A_193) | ~v5_relat_1(B_194, A_193) | ~v1_relat_1(B_194) | ~r1_tarski('#skF_7', k2_relat_1(B_194)) | ~r2_hidden(D_192, '#skF_6'))), inference(resolution, [status(thm)], [c_320, c_579])).
% 27.93/17.30  tff(c_671, plain, (![D_192, B_127, A_10]: (r2_hidden(k1_funct_1('#skF_8', D_192), B_127) | ~v1_relat_1(A_10) | ~r1_tarski('#skF_7', k2_relat_1(A_10)) | ~r2_hidden(D_192, '#skF_6') | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_286, c_645])).
% 27.93/17.30  tff(c_69074, plain, (![A_10]: (~v1_relat_1(A_10) | ~r1_tarski('#skF_7', k2_relat_1(A_10)) | ~r1_tarski(A_10, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_671])).
% 27.93/17.30  tff(c_81109, plain, (~v1_relat_1('#skF_8') | ~r1_tarski('#skF_7', '#skF_7') | ~r1_tarski('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_81089, c_69074])).
% 27.93/17.30  tff(c_81159, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_82, c_81109])).
% 27.93/17.30  tff(c_81396, plain, (![B_11521]: (k2_relat_1(k1_xboole_0)=k2_relat_1(B_11521) | ~v5_relat_1(B_11521, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(B_11521))), inference(resolution, [status(thm)], [c_68956, c_229])).
% 27.93/17.30  tff(c_81424, plain, (![A_132]: (k2_relat_1(k2_zfmisc_1(A_132, k2_relat_1(k1_xboole_0)))=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1(A_132, k2_relat_1(k1_xboole_0))))), inference(resolution, [status(thm)], [c_313, c_81396])).
% 27.93/17.30  tff(c_81448, plain, (![A_132]: (k2_relat_1(k2_zfmisc_1(A_132, k2_relat_1(k1_xboole_0)))=k2_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_81424])).
% 27.93/17.30  tff(c_81217, plain, (![D_11502, C_11503, B_11504, A_11505]: (m1_subset_1(D_11502, k1_zfmisc_1(k2_zfmisc_1(C_11503, B_11504))) | ~r1_tarski(k2_relat_1(D_11502), B_11504) | ~m1_subset_1(D_11502, k1_zfmisc_1(k2_zfmisc_1(C_11503, A_11505))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 27.93/17.30  tff(c_83023, plain, (![A_11603, C_11604, B_11605, A_11606]: (m1_subset_1(A_11603, k1_zfmisc_1(k2_zfmisc_1(C_11604, B_11605))) | ~r1_tarski(k2_relat_1(A_11603), B_11605) | ~r1_tarski(A_11603, k2_zfmisc_1(C_11604, A_11606)))), inference(resolution, [status(thm)], [c_22, c_81217])).
% 27.93/17.30  tff(c_83297, plain, (![A_11621, B_11622]: (m1_subset_1(A_11621, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_11621), B_11622))) | ~r1_tarski(k2_relat_1(A_11621), B_11622) | ~v1_relat_1(A_11621))), inference(resolution, [status(thm)], [c_32, c_83023])).
% 27.93/17.30  tff(c_83334, plain, (![A_11623]: (m1_subset_1(A_11623, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(A_11623), k1_xboole_0) | ~v1_relat_1(A_11623))), inference(superposition, [status(thm), theory('equality')], [c_16, c_83297])).
% 27.93/17.30  tff(c_83337, plain, (![A_132]: (m1_subset_1(k2_zfmisc_1(A_132, k2_relat_1(k1_xboole_0)), k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1(A_132, k2_relat_1(k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_81448, c_83334])).
% 27.93/17.30  tff(c_83367, plain, (![A_11624]: (m1_subset_1(k2_zfmisc_1(A_11624, k2_relat_1(k1_xboole_0)), k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_68954, c_83337])).
% 27.93/17.30  tff(c_83445, plain, (![A_11630]: (r1_tarski(k2_zfmisc_1(A_11630, k2_relat_1(k1_xboole_0)), k1_xboole_0))), inference(resolution, [status(thm)], [c_83367, c_20])).
% 27.93/17.30  tff(c_254, plain, (![A_121]: (k2_zfmisc_1(k1_relat_1(A_121), k2_relat_1(A_121))=A_121 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_121), k2_relat_1(A_121)), A_121) | ~v1_relat_1(A_121))), inference(resolution, [status(thm)], [c_239, c_8])).
% 27.93/17.30  tff(c_83449, plain, (k2_zfmisc_1(k1_relat_1(k1_xboole_0), k2_relat_1(k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_83445, c_254])).
% 27.93/17.30  tff(c_83473, plain, (k2_zfmisc_1(k1_relat_1(k1_xboole_0), k2_relat_1(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_119, c_83449])).
% 27.93/17.30  tff(c_83567, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_83473, c_14])).
% 27.93/17.30  tff(c_83591, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68861, c_83567])).
% 27.93/17.30  tff(c_81754, plain, (![A_11534, B_11535]: (r2_hidden('#skF_3'(A_11534, B_11535), k1_relat_1(A_11534)) | r2_hidden('#skF_4'(A_11534, B_11535), B_11535) | k2_relat_1(A_11534)=B_11535 | ~v1_funct_1(A_11534) | ~v1_relat_1(A_11534))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.30  tff(c_81772, plain, (![B_11535]: (r2_hidden('#skF_3'('#skF_8', B_11535), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_11535), B_11535) | k2_relat_1('#skF_8')=B_11535 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_81754])).
% 27.93/17.30  tff(c_81809, plain, (![B_11538]: (r2_hidden('#skF_3'('#skF_8', B_11538), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_11538), B_11538) | B_11538='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_81089, c_81772])).
% 27.93/17.30  tff(c_81973, plain, (![B_11548]: (~r1_tarski(B_11548, '#skF_4'('#skF_8', B_11548)) | r2_hidden('#skF_3'('#skF_8', B_11548), '#skF_6') | B_11548='#skF_7')), inference(resolution, [status(thm)], [c_81809, c_52])).
% 27.93/17.30  tff(c_81984, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1(k1_xboole_0)), '#skF_6') | k2_relat_1(k1_xboole_0)='#skF_7'), inference(resolution, [status(thm)], [c_68954, c_81973])).
% 27.93/17.30  tff(c_81986, plain, (k2_relat_1(k1_xboole_0)='#skF_7'), inference(splitLeft, [status(thm)], [c_81984])).
% 27.93/17.30  tff(c_30, plain, (![C_19, A_16, B_17]: (r2_hidden(C_19, A_16) | ~r2_hidden(C_19, k2_relat_1(B_17)) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 27.93/17.30  tff(c_81132, plain, (![C_19, A_16]: (r2_hidden(C_19, A_16) | ~r2_hidden(C_19, '#skF_7') | ~v5_relat_1('#skF_8', A_16) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_81089, c_30])).
% 27.93/17.30  tff(c_81336, plain, (![C_11514, A_11515]: (r2_hidden(C_11514, A_11515) | ~r2_hidden(C_11514, '#skF_7') | ~v5_relat_1('#skF_8', A_11515))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_81132])).
% 27.93/17.30  tff(c_81367, plain, (![D_11519, A_11520]: (r2_hidden(k1_funct_1('#skF_8', D_11519), A_11520) | ~v5_relat_1('#skF_8', A_11520) | ~r2_hidden(D_11519, '#skF_6'))), inference(resolution, [status(thm)], [c_76, c_81336])).
% 27.93/17.30  tff(c_81661, plain, (![A_11530, D_11531]: (~r1_tarski(A_11530, k1_funct_1('#skF_8', D_11531)) | ~v5_relat_1('#skF_8', A_11530) | ~r2_hidden(D_11531, '#skF_6'))), inference(resolution, [status(thm)], [c_81367, c_52])).
% 27.93/17.30  tff(c_81685, plain, (![D_11531]: (~v5_relat_1('#skF_8', k2_relat_1(k1_xboole_0)) | ~r2_hidden(D_11531, '#skF_6'))), inference(resolution, [status(thm)], [c_68954, c_81661])).
% 27.93/17.30  tff(c_81688, plain, (~v5_relat_1('#skF_8', k2_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_81685])).
% 27.93/17.30  tff(c_81987, plain, (~v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_81986, c_81688])).
% 27.93/17.30  tff(c_82005, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69545, c_81987])).
% 27.93/17.30  tff(c_82007, plain, (k2_relat_1(k1_xboole_0)!='#skF_7'), inference(splitRight, [status(thm)], [c_81984])).
% 27.93/17.30  tff(c_83614, plain, (k1_xboole_0!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_83591, c_82007])).
% 27.93/17.30  tff(c_456, plain, (![A_160, B_161, A_162]: (k1_relset_1(A_160, B_161, A_162)=k1_relat_1(A_162) | ~r1_tarski(A_162, k2_zfmisc_1(A_160, B_161)))), inference(resolution, [status(thm)], [c_22, c_375])).
% 27.93/17.30  tff(c_459, plain, (k1_relset_1('#skF_6', k2_relat_1('#skF_8'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_256, c_456])).
% 27.93/17.30  tff(c_478, plain, (k1_relset_1('#skF_6', k2_relat_1('#skF_8'), '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_459])).
% 27.93/17.30  tff(c_81097, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_81089, c_478])).
% 27.93/17.30  tff(c_81100, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_81089, c_256])).
% 27.93/17.30  tff(c_81354, plain, (![B_11516, C_11517, A_11518]: (k1_xboole_0=B_11516 | v1_funct_2(C_11517, A_11518, B_11516) | k1_relset_1(A_11518, B_11516, C_11517)!=A_11518 | ~m1_subset_1(C_11517, k1_zfmisc_1(k2_zfmisc_1(A_11518, B_11516))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 27.93/17.30  tff(c_83892, plain, (![B_11632, A_11633, A_11634]: (k1_xboole_0=B_11632 | v1_funct_2(A_11633, A_11634, B_11632) | k1_relset_1(A_11634, B_11632, A_11633)!=A_11634 | ~r1_tarski(A_11633, k2_zfmisc_1(A_11634, B_11632)))), inference(resolution, [status(thm)], [c_22, c_81354])).
% 27.93/17.30  tff(c_83906, plain, (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', '#skF_6', '#skF_7') | k1_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_6'), inference(resolution, [status(thm)], [c_81100, c_83892])).
% 27.93/17.30  tff(c_83933, plain, (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_81097, c_83906])).
% 27.93/17.30  tff(c_83935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_83614, c_83933])).
% 27.93/17.30  tff(c_83936, plain, (![D_11531]: (~r2_hidden(D_11531, '#skF_6'))), inference(splitRight, [status(thm)], [c_81685])).
% 27.93/17.30  tff(c_69483, plain, (![C_11006]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_11006), '#skF_6') | ~r2_hidden(C_11006, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_69477])).
% 27.93/17.30  tff(c_81096, plain, (![C_11006]: (r2_hidden('#skF_5'('#skF_8', '#skF_7', C_11006), '#skF_6') | ~r2_hidden(C_11006, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_81089, c_81089, c_69483])).
% 27.93/17.30  tff(c_83950, plain, (![C_11636]: (~r2_hidden(C_11636, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_83936, c_81096])).
% 27.93/17.30  tff(c_83960, plain, (![B_2]: (r1_tarski('#skF_7', B_2))), inference(resolution, [status(thm)], [c_6, c_83950])).
% 27.93/17.30  tff(c_81153, plain, (![A_12]: (v5_relat_1('#skF_8', A_12) | ~r1_tarski('#skF_7', A_12) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_81089, c_24])).
% 27.93/17.30  tff(c_81242, plain, (![A_11507]: (v5_relat_1('#skF_8', A_11507) | ~r1_tarski('#skF_7', A_11507))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_81153])).
% 27.93/17.30  tff(c_168, plain, (![C_101, A_102, B_103]: (v4_relat_1(C_101, A_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 27.93/17.30  tff(c_179, plain, (![A_10, A_102, B_103]: (v4_relat_1(A_10, A_102) | ~r1_tarski(A_10, k2_zfmisc_1(A_102, B_103)))), inference(resolution, [status(thm)], [c_22, c_168])).
% 27.93/17.30  tff(c_524, plain, (![B_168, A_169, B_170]: (v4_relat_1(k2_relat_1(B_168), A_169) | ~v5_relat_1(B_168, k2_zfmisc_1(A_169, B_170)) | ~v1_relat_1(B_168))), inference(resolution, [status(thm)], [c_212, c_179])).
% 27.93/17.30  tff(c_542, plain, (![B_168, A_8]: (v4_relat_1(k2_relat_1(B_168), A_8) | ~v5_relat_1(B_168, k1_xboole_0) | ~v1_relat_1(B_168))), inference(superposition, [status(thm), theory('equality')], [c_16, c_524])).
% 27.93/17.30  tff(c_81138, plain, (![A_8]: (v4_relat_1('#skF_7', A_8) | ~v5_relat_1('#skF_8', k1_xboole_0) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_81089, c_542])).
% 27.93/17.30  tff(c_81179, plain, (![A_8]: (v4_relat_1('#skF_7', A_8) | ~v5_relat_1('#skF_8', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_81138])).
% 27.93/17.30  tff(c_81237, plain, (~v5_relat_1('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_81179])).
% 27.93/17.30  tff(c_81263, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_81242, c_81237])).
% 27.93/17.30  tff(c_83973, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83960, c_81263])).
% 27.93/17.30  tff(c_83975, plain, (v5_relat_1('#skF_8', k1_xboole_0)), inference(splitRight, [status(thm)], [c_81179])).
% 27.93/17.30  tff(c_81147, plain, (![A_12]: (r1_tarski('#skF_7', A_12) | ~v5_relat_1('#skF_8', A_12) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_81089, c_26])).
% 27.93/17.30  tff(c_84015, plain, (![A_11639]: (r1_tarski('#skF_7', A_11639) | ~v5_relat_1('#skF_8', A_11639))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_81147])).
% 27.93/17.30  tff(c_84034, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_83975, c_84015])).
% 27.93/17.30  tff(c_85679, plain, (![A_11738, C_11739, B_11740, A_11741]: (m1_subset_1(A_11738, k1_zfmisc_1(k2_zfmisc_1(C_11739, B_11740))) | ~r1_tarski(k2_relat_1(A_11738), B_11740) | ~r1_tarski(A_11738, k2_zfmisc_1(C_11739, A_11741)))), inference(resolution, [status(thm)], [c_22, c_81217])).
% 27.93/17.30  tff(c_85681, plain, (![B_11740]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_11740))) | ~r1_tarski(k2_relat_1('#skF_8'), B_11740))), inference(resolution, [status(thm)], [c_81100, c_85679])).
% 27.93/17.30  tff(c_85824, plain, (![B_11747]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_11747))) | ~r1_tarski('#skF_7', B_11747))), inference(demodulation, [status(thm), theory('equality')], [c_81089, c_85681])).
% 27.93/17.30  tff(c_85848, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_85824])).
% 27.93/17.30  tff(c_85860, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_84034, c_85848])).
% 27.93/17.30  tff(c_85873, plain, (r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_85860, c_20])).
% 27.93/17.30  tff(c_85884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81159, c_85873])).
% 27.93/17.30  tff(c_86118, plain, (![D_11757, B_11758]: (r2_hidden(k1_funct_1('#skF_8', D_11757), B_11758) | ~r2_hidden(D_11757, '#skF_6'))), inference(splitRight, [status(thm)], [c_671])).
% 27.93/17.30  tff(c_86134, plain, (![B_11759, D_11760]: (~r1_tarski(B_11759, k1_funct_1('#skF_8', D_11760)) | ~r2_hidden(D_11760, '#skF_6'))), inference(resolution, [status(thm)], [c_86118, c_52])).
% 27.93/17.30  tff(c_86149, plain, (![D_11761]: (~r2_hidden(D_11761, '#skF_6'))), inference(resolution, [status(thm)], [c_68954, c_86134])).
% 27.93/17.30  tff(c_86159, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_86149])).
% 27.93/17.30  tff(c_86145, plain, (![D_11760]: (~r2_hidden(D_11760, '#skF_6'))), inference(resolution, [status(thm)], [c_68954, c_86134])).
% 27.93/17.30  tff(c_85973, plain, (![A_11750, C_11751]: (r2_hidden('#skF_5'(A_11750, k2_relat_1(A_11750), C_11751), k1_relat_1(A_11750)) | ~r2_hidden(C_11751, k2_relat_1(A_11750)) | ~v1_funct_1(A_11750) | ~v1_relat_1(A_11750))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.30  tff(c_85981, plain, (![C_11751]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_11751), '#skF_6') | ~r2_hidden(C_11751, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_85973])).
% 27.93/17.30  tff(c_85985, plain, (![C_11751]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_11751), '#skF_6') | ~r2_hidden(C_11751, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_85981])).
% 27.93/17.30  tff(c_86307, plain, (![C_11767]: (~r2_hidden(C_11767, k2_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_86145, c_85985])).
% 27.93/17.30  tff(c_86324, plain, (![B_2]: (r1_tarski(k2_relat_1('#skF_8'), B_2))), inference(resolution, [status(thm)], [c_6, c_86307])).
% 27.93/17.30  tff(c_86170, plain, (![B_11766]: (r1_tarski('#skF_6', B_11766))), inference(resolution, [status(thm)], [c_6, c_86149])).
% 27.93/17.30  tff(c_86545, plain, (![B_11778]: (B_11778='#skF_6' | ~r1_tarski(B_11778, '#skF_6'))), inference(resolution, [status(thm)], [c_86170, c_8])).
% 27.93/17.30  tff(c_86562, plain, (k2_relat_1('#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_86324, c_86545])).
% 27.93/17.30  tff(c_86574, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_86562, c_256])).
% 27.93/17.30  tff(c_86160, plain, (![D_11762, C_11763, B_11764, A_11765]: (m1_subset_1(D_11762, k1_zfmisc_1(k2_zfmisc_1(C_11763, B_11764))) | ~r1_tarski(k2_relat_1(D_11762), B_11764) | ~m1_subset_1(D_11762, k1_zfmisc_1(k2_zfmisc_1(C_11763, A_11765))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 27.93/17.30  tff(c_88527, plain, (![A_11870, C_11871, B_11872, A_11873]: (m1_subset_1(A_11870, k1_zfmisc_1(k2_zfmisc_1(C_11871, B_11872))) | ~r1_tarski(k2_relat_1(A_11870), B_11872) | ~r1_tarski(A_11870, k2_zfmisc_1(C_11871, A_11873)))), inference(resolution, [status(thm)], [c_22, c_86160])).
% 27.93/17.30  tff(c_88548, plain, (![B_11872]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_11872))) | ~r1_tarski(k2_relat_1('#skF_8'), B_11872))), inference(resolution, [status(thm)], [c_86574, c_88527])).
% 27.93/17.30  tff(c_88653, plain, (![B_11876]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_11876))))), inference(demodulation, [status(thm), theory('equality')], [c_86159, c_86562, c_88548])).
% 27.93/17.30  tff(c_88664, plain, (![B_11876]: (k1_relset_1('#skF_6', B_11876, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_88653, c_58])).
% 27.93/17.30  tff(c_88683, plain, (![B_11876]: (k1_relset_1('#skF_6', B_11876, '#skF_8')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_88664])).
% 27.93/17.30  tff(c_88677, plain, (![B_11876]: (k1_xboole_0=B_11876 | v1_funct_2('#skF_8', '#skF_6', B_11876) | k1_relset_1('#skF_6', B_11876, '#skF_8')!='#skF_6')), inference(resolution, [status(thm)], [c_88653, c_68])).
% 27.93/17.30  tff(c_89164, plain, (![B_11900]: (k1_xboole_0=B_11900 | v1_funct_2('#skF_8', '#skF_6', B_11900))), inference(demodulation, [status(thm), theory('equality')], [c_88683, c_88677])).
% 27.93/17.30  tff(c_89176, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_89164, c_167])).
% 27.93/17.30  tff(c_89232, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_89176, c_89176, c_16])).
% 27.93/17.30  tff(c_86899, plain, (![B_11800]: (k2_relat_1(B_11800)='#skF_6' | ~v5_relat_1(B_11800, '#skF_6') | ~v1_relat_1(B_11800))), inference(resolution, [status(thm)], [c_86170, c_229])).
% 27.93/17.30  tff(c_86927, plain, (![A_132]: (k2_relat_1(k2_zfmisc_1(A_132, '#skF_6'))='#skF_6' | ~v1_relat_1(k2_zfmisc_1(A_132, '#skF_6')))), inference(resolution, [status(thm)], [c_313, c_86899])).
% 27.93/17.30  tff(c_86946, plain, (![A_132]: (k2_relat_1(k2_zfmisc_1(A_132, '#skF_6'))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_86927])).
% 27.93/17.30  tff(c_86948, plain, (![A_11801]: (k2_relat_1(k2_zfmisc_1(A_11801, '#skF_6'))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_86927])).
% 27.93/17.30  tff(c_86985, plain, (![A_11801]: (r1_tarski(k2_zfmisc_1(A_11801, '#skF_6'), k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_11801, '#skF_6')), '#skF_6')) | ~v1_relat_1(k2_zfmisc_1(A_11801, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_86948, c_32])).
% 27.93/17.30  tff(c_87025, plain, (![A_11801]: (r1_tarski(k2_zfmisc_1(A_11801, '#skF_6'), k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_11801, '#skF_6')), '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_86985])).
% 27.93/17.30  tff(c_88538, plain, (![A_11801, B_11872]: (m1_subset_1(k2_zfmisc_1(A_11801, '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_11801, '#skF_6')), B_11872))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(A_11801, '#skF_6')), B_11872))), inference(resolution, [status(thm)], [c_87025, c_88527])).
% 27.93/17.30  tff(c_91102, plain, (![A_11991, B_11992]: (m1_subset_1(k2_zfmisc_1(A_11991, '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_11991, '#skF_6')), B_11992))))), inference(demodulation, [status(thm), theory('equality')], [c_86159, c_86946, c_88538])).
% 27.93/17.30  tff(c_91139, plain, (![A_11993]: (m1_subset_1(k2_zfmisc_1(A_11993, '#skF_6'), k1_zfmisc_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_89232, c_91102])).
% 27.93/17.30  tff(c_91159, plain, (![A_11993]: (r1_tarski(k2_zfmisc_1(A_11993, '#skF_6'), '#skF_7'))), inference(resolution, [status(thm)], [c_91139, c_20])).
% 27.93/17.30  tff(c_86212, plain, (k2_relat_1(k1_xboole_0)='#skF_6'), inference(resolution, [status(thm)], [c_86170, c_69014])).
% 27.93/17.30  tff(c_86265, plain, (r1_tarski(k1_xboole_0, k2_zfmisc_1(k1_relat_1(k1_xboole_0), '#skF_6')) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_86212, c_32])).
% 27.93/17.30  tff(c_86299, plain, (r1_tarski(k1_xboole_0, k2_zfmisc_1(k1_relat_1(k1_xboole_0), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_86265])).
% 27.93/17.30  tff(c_86816, plain, (k2_zfmisc_1(k1_relat_1(k1_xboole_0), '#skF_6')=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0), '#skF_6'), k1_xboole_0)), inference(resolution, [status(thm)], [c_86299, c_8])).
% 27.93/17.30  tff(c_87718, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0), '#skF_6'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_86816])).
% 27.93/17.30  tff(c_89198, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_7'), '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_89176, c_89176, c_87718])).
% 27.93/17.30  tff(c_91169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91159, c_89198])).
% 27.93/17.30  tff(c_91170, plain, (k2_zfmisc_1(k1_relat_1(k1_xboole_0), '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_86816])).
% 27.93/17.30  tff(c_91257, plain, (k1_xboole_0='#skF_6' | k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_91170, c_14])).
% 27.93/17.30  tff(c_91280, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_68861, c_91257])).
% 27.93/17.30  tff(c_91318, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_91280, c_91280, c_16])).
% 27.93/17.30  tff(c_263, plain, (k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8'))='#skF_8' | ~r1_tarski(k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8')), '#skF_8')), inference(resolution, [status(thm)], [c_256, c_8])).
% 27.93/17.30  tff(c_287, plain, (~r1_tarski(k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8')), '#skF_8')), inference(splitLeft, [status(thm)], [c_263])).
% 27.93/17.30  tff(c_86573, plain, (~r1_tarski(k2_zfmisc_1('#skF_6', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_86562, c_287])).
% 27.93/17.30  tff(c_91376, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_91318, c_86573])).
% 27.93/17.30  tff(c_91385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86159, c_91376])).
% 27.93/17.30  tff(c_91387, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_68859])).
% 27.93/17.30  tff(c_34, plain, (![A_21, D_60]: (r2_hidden(k1_funct_1(A_21, D_60), k2_relat_1(A_21)) | ~r2_hidden(D_60, k1_relat_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.30  tff(c_31187, plain, (![A_5911, C_5912]: (r2_hidden('#skF_5'(A_5911, k2_relat_1(A_5911), C_5912), k1_relat_1(A_5911)) | ~r2_hidden(C_5912, k2_relat_1(A_5911)) | ~v1_funct_1(A_5911) | ~v1_relat_1(A_5911))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.30  tff(c_31198, plain, (![C_5912]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_5912), '#skF_6') | ~r2_hidden(C_5912, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_31187])).
% 27.93/17.30  tff(c_31204, plain, (![C_5912]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_5912), '#skF_6') | ~r2_hidden(C_5912, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_31198])).
% 27.93/17.30  tff(c_31524, plain, (![A_5924, C_5925]: (k1_funct_1(A_5924, '#skF_5'(A_5924, k2_relat_1(A_5924), C_5925))=C_5925 | ~r2_hidden(C_5925, k2_relat_1(A_5924)) | ~v1_funct_1(A_5924) | ~v1_relat_1(A_5924))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.30  tff(c_31554, plain, (![C_5925]: (r2_hidden(C_5925, '#skF_7') | ~r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_5925), '#skF_6') | ~r2_hidden(C_5925, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_31524, c_76])).
% 27.93/17.30  tff(c_31608, plain, (![C_5931]: (r2_hidden(C_5931, '#skF_7') | ~r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_5931), '#skF_6') | ~r2_hidden(C_5931, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_31554])).
% 27.93/17.30  tff(c_31613, plain, (![C_5932]: (r2_hidden(C_5932, '#skF_7') | ~r2_hidden(C_5932, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_31204, c_31608])).
% 27.93/17.30  tff(c_31636, plain, (![B_5933]: (r2_hidden('#skF_1'(k2_relat_1('#skF_8'), B_5933), '#skF_7') | r1_tarski(k2_relat_1('#skF_8'), B_5933))), inference(resolution, [status(thm)], [c_6, c_31613])).
% 27.93/17.30  tff(c_31647, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_31636, c_4])).
% 27.93/17.30  tff(c_32047, plain, (![B_5965, B_5966]: (r2_hidden('#skF_1'(k2_relat_1('#skF_8'), B_5965), B_5966) | ~r1_tarski('#skF_7', B_5966) | r1_tarski(k2_relat_1('#skF_8'), B_5965))), inference(resolution, [status(thm)], [c_31636, c_2])).
% 27.93/17.30  tff(c_32096, plain, (![B_5969]: (~r1_tarski('#skF_7', B_5969) | r1_tarski(k2_relat_1('#skF_8'), B_5969))), inference(resolution, [status(thm)], [c_32047, c_4])).
% 27.93/17.30  tff(c_275, plain, (![A_10, B_123, A_124]: (v5_relat_1(A_10, B_123) | ~r1_tarski(A_10, k2_zfmisc_1(A_124, B_123)))), inference(resolution, [status(thm)], [c_22, c_264])).
% 27.93/17.30  tff(c_32234, plain, (![B_5971, A_5972]: (v5_relat_1(k2_relat_1('#skF_8'), B_5971) | ~r1_tarski('#skF_7', k2_zfmisc_1(A_5972, B_5971)))), inference(resolution, [status(thm)], [c_32096, c_275])).
% 27.93/17.30  tff(c_32242, plain, (v5_relat_1(k2_relat_1('#skF_8'), k2_relat_1('#skF_7')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_32234])).
% 27.93/17.30  tff(c_32243, plain, (~v1_relat_1('#skF_7')), inference(splitLeft, [status(thm)], [c_32242])).
% 27.93/17.30  tff(c_780, plain, (![B_211, B_212]: (r1_tarski(k2_relat_1(B_211), B_212) | ~v5_relat_1(B_211, '#skF_1'(k2_relat_1(B_211), B_212)) | ~v1_relat_1(B_211))), inference(resolution, [status(thm)], [c_212, c_153])).
% 27.93/17.30  tff(c_807, plain, (![A_10, B_212]: (r1_tarski(k2_relat_1(A_10), B_212) | ~v1_relat_1(A_10) | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_286, c_780])).
% 27.93/17.30  tff(c_31101, plain, (![A_5902, D_5903]: (r2_hidden(k1_funct_1(A_5902, D_5903), k2_relat_1(A_5902)) | ~r2_hidden(D_5903, k1_relat_1(A_5902)) | ~v1_funct_1(A_5902) | ~v1_relat_1(A_5902))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.30  tff(c_40069, plain, (![A_6304, D_6305]: (~r1_tarski(k2_relat_1(A_6304), k1_funct_1(A_6304, D_6305)) | ~r2_hidden(D_6305, k1_relat_1(A_6304)) | ~v1_funct_1(A_6304) | ~v1_relat_1(A_6304))), inference(resolution, [status(thm)], [c_31101, c_52])).
% 27.93/17.30  tff(c_40110, plain, (![D_6306, A_6307]: (~r2_hidden(D_6306, k1_relat_1(A_6307)) | ~v1_funct_1(A_6307) | ~v1_relat_1(A_6307) | ~r1_tarski(A_6307, k1_xboole_0))), inference(resolution, [status(thm)], [c_807, c_40069])).
% 27.93/17.30  tff(c_40178, plain, (![D_6306]: (~r2_hidden(D_6306, '#skF_6') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_78, c_40110])).
% 27.93/17.30  tff(c_40198, plain, (![D_6306]: (~r2_hidden(D_6306, '#skF_6') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_40178])).
% 27.93/17.30  tff(c_40199, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_40198])).
% 27.93/17.30  tff(c_35185, plain, (![A_6103, D_6104]: (~r1_tarski(k2_relat_1(A_6103), k1_funct_1(A_6103, D_6104)) | ~r2_hidden(D_6104, k1_relat_1(A_6103)) | ~v1_funct_1(A_6103) | ~v1_relat_1(A_6103))), inference(resolution, [status(thm)], [c_31101, c_52])).
% 27.93/17.30  tff(c_35231, plain, (![D_6105, A_6106]: (~r2_hidden(D_6105, k1_relat_1(A_6106)) | ~v1_funct_1(A_6106) | ~v1_relat_1(A_6106) | ~r1_tarski(A_6106, k1_xboole_0))), inference(resolution, [status(thm)], [c_807, c_35185])).
% 27.93/17.30  tff(c_35295, plain, (![D_6105]: (~r2_hidden(D_6105, '#skF_6') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_78, c_35231])).
% 27.93/17.30  tff(c_35314, plain, (![D_6105]: (~r2_hidden(D_6105, '#skF_6') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_35295])).
% 27.93/17.30  tff(c_35315, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_35314])).
% 27.93/17.30  tff(c_31653, plain, (v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_31647, c_24])).
% 27.93/17.30  tff(c_31659, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_31653])).
% 27.93/17.30  tff(c_31667, plain, (![D_5934, C_5935, B_5936, A_5937]: (m1_subset_1(D_5934, k1_zfmisc_1(k2_zfmisc_1(C_5935, B_5936))) | ~r1_tarski(k2_relat_1(D_5934), B_5936) | ~m1_subset_1(D_5934, k1_zfmisc_1(k2_zfmisc_1(C_5935, A_5937))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 27.93/17.30  tff(c_36278, plain, (![A_6153, C_6154, B_6155, A_6156]: (m1_subset_1(A_6153, k1_zfmisc_1(k2_zfmisc_1(C_6154, B_6155))) | ~r1_tarski(k2_relat_1(A_6153), B_6155) | ~r1_tarski(A_6153, k2_zfmisc_1(C_6154, A_6156)))), inference(resolution, [status(thm)], [c_22, c_31667])).
% 27.93/17.30  tff(c_36415, plain, (![B_6163]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_6163))) | ~r1_tarski(k2_relat_1('#skF_8'), B_6163))), inference(resolution, [status(thm)], [c_256, c_36278])).
% 27.93/17.30  tff(c_36426, plain, (![B_6163]: (k1_relset_1('#skF_6', B_6163, '#skF_8')=k1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), B_6163))), inference(resolution, [status(thm)], [c_36415, c_58])).
% 27.93/17.30  tff(c_36514, plain, (![B_6165]: (k1_relset_1('#skF_6', B_6165, '#skF_8')='#skF_6' | ~r1_tarski(k2_relat_1('#skF_8'), B_6165))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_36426])).
% 27.93/17.30  tff(c_36543, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_31647, c_36514])).
% 27.93/17.30  tff(c_36682, plain, (![B_6171]: (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', B_6171)) | ~r1_tarski(k2_relat_1('#skF_8'), B_6171))), inference(resolution, [status(thm)], [c_36415, c_20])).
% 27.93/17.30  tff(c_36711, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_31647, c_36682])).
% 27.93/17.30  tff(c_32244, plain, (![B_5973, C_5974, A_5975]: (k1_xboole_0=B_5973 | v1_funct_2(C_5974, A_5975, B_5973) | k1_relset_1(A_5975, B_5973, C_5974)!=A_5975 | ~m1_subset_1(C_5974, k1_zfmisc_1(k2_zfmisc_1(A_5975, B_5973))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 27.93/17.30  tff(c_32255, plain, (![B_5973, A_10, A_5975]: (k1_xboole_0=B_5973 | v1_funct_2(A_10, A_5975, B_5973) | k1_relset_1(A_5975, B_5973, A_10)!=A_5975 | ~r1_tarski(A_10, k2_zfmisc_1(A_5975, B_5973)))), inference(resolution, [status(thm)], [c_22, c_32244])).
% 27.93/17.30  tff(c_36723, plain, (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', '#skF_6', '#skF_7') | k1_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_6'), inference(resolution, [status(thm)], [c_36711, c_32255])).
% 27.93/17.30  tff(c_36743, plain, (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_36543, c_36723])).
% 27.93/17.30  tff(c_36744, plain, (k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_167, c_36743])).
% 27.93/17.30  tff(c_35567, plain, (![D_6113, A_6114, B_6115]: (m1_subset_1(D_6113, k1_zfmisc_1(k2_zfmisc_1(A_6114, B_6115))) | ~r1_tarski(k2_relat_1(D_6113), B_6115) | ~m1_subset_1(D_6113, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_31667])).
% 27.93/17.30  tff(c_35786, plain, (![D_6125, A_6126, B_6127]: (r1_tarski(D_6125, k2_zfmisc_1(A_6126, B_6127)) | ~r1_tarski(k2_relat_1(D_6125), B_6127) | ~m1_subset_1(D_6125, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_35567, c_20])).
% 27.93/17.30  tff(c_35815, plain, (![A_6126]: (r1_tarski('#skF_8', k2_zfmisc_1(A_6126, '#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_31647, c_35786])).
% 27.93/17.30  tff(c_35877, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_35815])).
% 27.93/17.30  tff(c_36439, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_36415])).
% 27.93/17.30  tff(c_36449, plain, (~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_35877, c_36439])).
% 27.93/17.30  tff(c_36458, plain, (~v5_relat_1('#skF_8', k1_xboole_0) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_26, c_36449])).
% 27.93/17.30  tff(c_36465, plain, (~v5_relat_1('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_36458])).
% 27.93/17.30  tff(c_36756, plain, (~v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_36744, c_36465])).
% 27.93/17.30  tff(c_36856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31659, c_36756])).
% 27.93/17.30  tff(c_36858, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_35815])).
% 27.93/17.30  tff(c_36913, plain, (r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_36858, c_20])).
% 27.93/17.30  tff(c_36924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35315, c_36913])).
% 27.93/17.30  tff(c_36925, plain, (![D_6105]: (~r2_hidden(D_6105, '#skF_6'))), inference(splitRight, [status(thm)], [c_35314])).
% 27.93/17.30  tff(c_796, plain, (![B_212]: (r1_tarski(k2_relat_1(k1_xboole_0), B_212) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_324, c_780])).
% 27.93/17.30  tff(c_806, plain, (![B_212]: (r1_tarski(k2_relat_1(k1_xboole_0), B_212))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_796])).
% 27.93/17.30  tff(c_32293, plain, (![A_5979, B_5980]: (r2_hidden('#skF_3'(A_5979, B_5980), k1_relat_1(A_5979)) | r2_hidden('#skF_4'(A_5979, B_5980), B_5980) | k2_relat_1(A_5979)=B_5980 | ~v1_funct_1(A_5979) | ~v1_relat_1(A_5979))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.30  tff(c_32316, plain, (![B_5980]: (r2_hidden('#skF_3'('#skF_8', B_5980), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_5980), B_5980) | k2_relat_1('#skF_8')=B_5980 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_32293])).
% 27.93/17.30  tff(c_32326, plain, (![B_5981]: (r2_hidden('#skF_3'('#skF_8', B_5981), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_5981), B_5981) | k2_relat_1('#skF_8')=B_5981)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_32316])).
% 27.93/17.30  tff(c_32381, plain, (![B_5983]: (~r1_tarski(B_5983, '#skF_4'('#skF_8', B_5983)) | r2_hidden('#skF_3'('#skF_8', B_5983), '#skF_6') | k2_relat_1('#skF_8')=B_5983)), inference(resolution, [status(thm)], [c_32326, c_52])).
% 27.93/17.30  tff(c_32397, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1(k1_xboole_0)), '#skF_6') | k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_806, c_32381])).
% 27.93/17.30  tff(c_32399, plain, (k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_32397])).
% 27.93/17.30  tff(c_32408, plain, (![B_212]: (r1_tarski(k2_relat_1('#skF_8'), B_212))), inference(demodulation, [status(thm), theory('equality')], [c_32399, c_806])).
% 27.93/17.30  tff(c_32459, plain, (![C_19, A_16]: (r2_hidden(C_19, A_16) | ~r2_hidden(C_19, k2_relat_1('#skF_8')) | ~v5_relat_1(k1_xboole_0, A_16) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32399, c_30])).
% 27.93/17.30  tff(c_32915, plain, (![C_6005, A_6006]: (r2_hidden(C_6005, A_6006) | ~r2_hidden(C_6005, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_324, c_32459])).
% 27.93/17.30  tff(c_32940, plain, (![D_60, A_6006]: (r2_hidden(k1_funct_1('#skF_8', D_60), A_6006) | ~r2_hidden(D_60, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_34, c_32915])).
% 27.93/17.30  tff(c_33210, plain, (![D_6014, A_6015]: (r2_hidden(k1_funct_1('#skF_8', D_6014), A_6015) | ~r2_hidden(D_6014, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_32940])).
% 27.93/17.30  tff(c_33241, plain, (![A_6016, D_6017]: (~r1_tarski(A_6016, k1_funct_1('#skF_8', D_6017)) | ~r2_hidden(D_6017, '#skF_6'))), inference(resolution, [status(thm)], [c_33210, c_52])).
% 27.93/17.30  tff(c_33271, plain, (![D_6018]: (~r2_hidden(D_6018, '#skF_6'))), inference(resolution, [status(thm)], [c_32408, c_33241])).
% 27.93/17.30  tff(c_33309, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_33271])).
% 27.93/17.30  tff(c_33357, plain, (![B_6020]: (r1_tarski('#skF_6', B_6020))), inference(resolution, [status(thm)], [c_6, c_33271])).
% 27.93/17.30  tff(c_808, plain, (![B_213]: (r1_tarski(k2_relat_1(k1_xboole_0), B_213))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_796])).
% 27.93/17.30  tff(c_866, plain, (![B_213]: (k2_relat_1(k1_xboole_0)=B_213 | ~r1_tarski(B_213, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_808, c_8])).
% 27.93/17.30  tff(c_32407, plain, (![B_213]: (k2_relat_1('#skF_8')=B_213 | ~r1_tarski(B_213, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_32399, c_32399, c_866])).
% 27.93/17.30  tff(c_33406, plain, (k2_relat_1('#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_33357, c_32407])).
% 27.93/17.30  tff(c_33435, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_33406, c_256])).
% 27.93/17.30  tff(c_34130, plain, (![A_6043, C_6044, B_6045, A_6046]: (m1_subset_1(A_6043, k1_zfmisc_1(k2_zfmisc_1(C_6044, B_6045))) | ~r1_tarski(k2_relat_1(A_6043), B_6045) | ~r1_tarski(A_6043, k2_zfmisc_1(C_6044, A_6046)))), inference(resolution, [status(thm)], [c_22, c_31667])).
% 27.93/17.30  tff(c_34132, plain, (![B_6045]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_6045))) | ~r1_tarski(k2_relat_1('#skF_8'), B_6045))), inference(resolution, [status(thm)], [c_33435, c_34130])).
% 27.93/17.30  tff(c_34162, plain, (![B_6047]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_6047))))), inference(demodulation, [status(thm), theory('equality')], [c_33309, c_33406, c_34132])).
% 27.93/17.30  tff(c_34173, plain, (![B_6047]: (k1_relset_1('#skF_6', B_6047, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_34162, c_58])).
% 27.93/17.30  tff(c_34192, plain, (![B_6047]: (k1_relset_1('#skF_6', B_6047, '#skF_8')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_34173])).
% 27.93/17.30  tff(c_34197, plain, (![B_6047]: (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', B_6047)))), inference(resolution, [status(thm)], [c_34162, c_20])).
% 27.93/17.30  tff(c_34331, plain, (![B_6054, A_6055, A_6056]: (k1_xboole_0=B_6054 | v1_funct_2(A_6055, A_6056, B_6054) | k1_relset_1(A_6056, B_6054, A_6055)!=A_6056 | ~r1_tarski(A_6055, k2_zfmisc_1(A_6056, B_6054)))), inference(resolution, [status(thm)], [c_22, c_32244])).
% 27.93/17.30  tff(c_34334, plain, (![B_6047]: (k1_xboole_0=B_6047 | v1_funct_2('#skF_8', '#skF_6', B_6047) | k1_relset_1('#skF_6', B_6047, '#skF_8')!='#skF_6')), inference(resolution, [status(thm)], [c_34197, c_34331])).
% 27.93/17.30  tff(c_34377, plain, (![B_6057]: (k1_xboole_0=B_6057 | v1_funct_2('#skF_8', '#skF_6', B_6057))), inference(demodulation, [status(thm), theory('equality')], [c_34192, c_34334])).
% 27.93/17.30  tff(c_34388, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_34377, c_167])).
% 27.93/17.30  tff(c_32239, plain, (![B_9]: (v5_relat_1(k2_relat_1('#skF_8'), B_9) | ~r1_tarski('#skF_7', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_32234])).
% 27.93/17.30  tff(c_32257, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_32239])).
% 27.93/17.30  tff(c_34398, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_34388, c_32257])).
% 27.93/17.30  tff(c_34440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_34398])).
% 27.93/17.30  tff(c_34441, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1(k1_xboole_0)), '#skF_6')), inference(splitRight, [status(thm)], [c_32397])).
% 27.93/17.30  tff(c_36932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36925, c_34441])).
% 27.93/17.30  tff(c_36934, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_32239])).
% 27.93/17.30  tff(c_32072, plain, (![B_5966]: (~r1_tarski('#skF_7', B_5966) | r1_tarski(k2_relat_1('#skF_8'), B_5966))), inference(resolution, [status(thm)], [c_32047, c_4])).
% 27.93/17.30  tff(c_40457, plain, (![D_6314, A_6315, B_6316]: (m1_subset_1(D_6314, k1_zfmisc_1(k2_zfmisc_1(A_6315, B_6316))) | ~r1_tarski(k2_relat_1(D_6314), B_6316) | ~m1_subset_1(D_6314, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_31667])).
% 27.93/17.30  tff(c_40702, plain, (![D_6328, A_6329, B_6330]: (r1_tarski(D_6328, k2_zfmisc_1(A_6329, B_6330)) | ~r1_tarski(k2_relat_1(D_6328), B_6330) | ~m1_subset_1(D_6328, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_40457, c_20])).
% 27.93/17.30  tff(c_40728, plain, (![A_6329]: (r1_tarski('#skF_8', k2_zfmisc_1(A_6329, '#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_31647, c_40702])).
% 27.93/17.30  tff(c_40792, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_40728])).
% 27.93/17.30  tff(c_40845, plain, (![A_6339, C_6340, B_6341, A_6342]: (m1_subset_1(A_6339, k1_zfmisc_1(k2_zfmisc_1(C_6340, B_6341))) | ~r1_tarski(k2_relat_1(A_6339), B_6341) | ~r1_tarski(A_6339, k2_zfmisc_1(C_6340, A_6342)))), inference(resolution, [status(thm)], [c_22, c_31667])).
% 27.93/17.30  tff(c_40973, plain, (![B_6349]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_6349))) | ~r1_tarski(k2_relat_1('#skF_8'), B_6349))), inference(resolution, [status(thm)], [c_256, c_40845])).
% 27.93/17.30  tff(c_40997, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_40973])).
% 27.93/17.30  tff(c_41007, plain, (~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_40792, c_40997])).
% 27.93/17.30  tff(c_41010, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_32072, c_41007])).
% 27.93/17.30  tff(c_41020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36934, c_41010])).
% 27.93/17.30  tff(c_41022, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_40728])).
% 27.93/17.30  tff(c_41035, plain, (r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_41022, c_20])).
% 27.93/17.30  tff(c_41046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40199, c_41035])).
% 27.93/17.30  tff(c_41047, plain, (![D_6306]: (~r2_hidden(D_6306, '#skF_6'))), inference(splitRight, [status(thm)], [c_40198])).
% 27.93/17.30  tff(c_37014, plain, (![A_6178, B_6179]: (r2_hidden('#skF_3'(A_6178, B_6179), k1_relat_1(A_6178)) | r2_hidden('#skF_4'(A_6178, B_6179), B_6179) | k2_relat_1(A_6178)=B_6179 | ~v1_funct_1(A_6178) | ~v1_relat_1(A_6178))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.30  tff(c_37037, plain, (![B_6179]: (r2_hidden('#skF_3'('#skF_8', B_6179), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_6179), B_6179) | k2_relat_1('#skF_8')=B_6179 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_37014])).
% 27.93/17.30  tff(c_37050, plain, (![B_6180]: (r2_hidden('#skF_3'('#skF_8', B_6180), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_6180), B_6180) | k2_relat_1('#skF_8')=B_6180)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_37037])).
% 27.93/17.30  tff(c_37356, plain, (![B_6195]: (~r1_tarski(B_6195, '#skF_4'('#skF_8', B_6195)) | r2_hidden('#skF_3'('#skF_8', B_6195), '#skF_6') | k2_relat_1('#skF_8')=B_6195)), inference(resolution, [status(thm)], [c_37050, c_52])).
% 27.93/17.30  tff(c_37372, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1(k1_xboole_0)), '#skF_6') | k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_806, c_37356])).
% 27.93/17.30  tff(c_37374, plain, (k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_37372])).
% 27.93/17.30  tff(c_37383, plain, (![B_212]: (r1_tarski(k2_relat_1('#skF_8'), B_212))), inference(demodulation, [status(thm), theory('equality')], [c_37374, c_806])).
% 27.93/17.30  tff(c_37436, plain, (![C_19, A_16]: (r2_hidden(C_19, A_16) | ~r2_hidden(C_19, k2_relat_1('#skF_8')) | ~v5_relat_1(k1_xboole_0, A_16) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_37374, c_30])).
% 27.93/17.30  tff(c_37897, plain, (![C_6212, A_6213]: (r2_hidden(C_6212, A_6213) | ~r2_hidden(C_6212, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_324, c_37436])).
% 27.93/17.30  tff(c_37916, plain, (![D_60, A_6213]: (r2_hidden(k1_funct_1('#skF_8', D_60), A_6213) | ~r2_hidden(D_60, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_34, c_37897])).
% 27.93/17.30  tff(c_38094, plain, (![D_6221, A_6222]: (r2_hidden(k1_funct_1('#skF_8', D_6221), A_6222) | ~r2_hidden(D_6221, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_37916])).
% 27.93/17.30  tff(c_38123, plain, (![A_6223, D_6224]: (~r1_tarski(A_6223, k1_funct_1('#skF_8', D_6224)) | ~r2_hidden(D_6224, '#skF_6'))), inference(resolution, [status(thm)], [c_38094, c_52])).
% 27.93/17.30  tff(c_38153, plain, (![D_6225]: (~r2_hidden(D_6225, '#skF_6'))), inference(resolution, [status(thm)], [c_37383, c_38123])).
% 27.93/17.30  tff(c_38191, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_38153])).
% 27.93/17.30  tff(c_38200, plain, (![B_6226]: (r1_tarski('#skF_6', B_6226))), inference(resolution, [status(thm)], [c_6, c_38153])).
% 27.93/17.30  tff(c_37382, plain, (![B_213]: (k2_relat_1('#skF_8')=B_213 | ~r1_tarski(B_213, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_37374, c_37374, c_866])).
% 27.93/17.30  tff(c_38249, plain, (k2_relat_1('#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_38200, c_37382])).
% 27.93/17.30  tff(c_38279, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_38249, c_256])).
% 27.93/17.30  tff(c_38911, plain, (![A_6244, C_6245, B_6246, A_6247]: (m1_subset_1(A_6244, k1_zfmisc_1(k2_zfmisc_1(C_6245, B_6246))) | ~r1_tarski(k2_relat_1(A_6244), B_6246) | ~r1_tarski(A_6244, k2_zfmisc_1(C_6245, A_6247)))), inference(resolution, [status(thm)], [c_22, c_31667])).
% 27.93/17.30  tff(c_38913, plain, (![B_6246]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_6246))) | ~r1_tarski(k2_relat_1('#skF_8'), B_6246))), inference(resolution, [status(thm)], [c_38279, c_38911])).
% 27.93/17.30  tff(c_38944, plain, (![B_6248]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_6248))))), inference(demodulation, [status(thm), theory('equality')], [c_38191, c_38249, c_38913])).
% 27.93/17.30  tff(c_38955, plain, (![B_6248]: (k1_relset_1('#skF_6', B_6248, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_38944, c_58])).
% 27.93/17.30  tff(c_38974, plain, (![B_6248]: (k1_relset_1('#skF_6', B_6248, '#skF_8')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_38955])).
% 27.93/17.30  tff(c_38979, plain, (![B_6248]: (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', B_6248)))), inference(resolution, [status(thm)], [c_38944, c_20])).
% 27.93/17.30  tff(c_39311, plain, (![B_6265, A_6266, A_6267]: (k1_xboole_0=B_6265 | v1_funct_2(A_6266, A_6267, B_6265) | k1_relset_1(A_6267, B_6265, A_6266)!=A_6267 | ~r1_tarski(A_6266, k2_zfmisc_1(A_6267, B_6265)))), inference(resolution, [status(thm)], [c_22, c_32244])).
% 27.93/17.30  tff(c_39314, plain, (![B_6248]: (k1_xboole_0=B_6248 | v1_funct_2('#skF_8', '#skF_6', B_6248) | k1_relset_1('#skF_6', B_6248, '#skF_8')!='#skF_6')), inference(resolution, [status(thm)], [c_38979, c_39311])).
% 27.93/17.30  tff(c_39351, plain, (![B_6268]: (k1_xboole_0=B_6268 | v1_funct_2('#skF_8', '#skF_6', B_6268))), inference(demodulation, [status(thm), theory('equality')], [c_38974, c_39314])).
% 27.93/17.30  tff(c_39362, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_39351, c_167])).
% 27.93/17.30  tff(c_36952, plain, (k1_xboole_0='#skF_7' | ~r1_tarski(k1_xboole_0, '#skF_7')), inference(resolution, [status(thm)], [c_36934, c_8])).
% 27.93/17.30  tff(c_36991, plain, (~r1_tarski(k1_xboole_0, '#skF_7')), inference(splitLeft, [status(thm)], [c_36952])).
% 27.93/17.30  tff(c_39375, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_39362, c_36991])).
% 27.93/17.30  tff(c_39418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_39375])).
% 27.93/17.30  tff(c_39419, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1(k1_xboole_0)), '#skF_6')), inference(splitRight, [status(thm)], [c_37372])).
% 27.93/17.30  tff(c_41054, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41047, c_39419])).
% 27.93/17.30  tff(c_41055, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_36952])).
% 27.93/17.30  tff(c_41107, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_41055, c_119])).
% 27.93/17.30  tff(c_41112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32243, c_41107])).
% 27.93/17.30  tff(c_41114, plain, (v1_relat_1('#skF_7')), inference(splitRight, [status(thm)], [c_32242])).
% 27.93/17.30  tff(c_41143, plain, (![A_6355, B_6356]: (r2_hidden('#skF_3'(A_6355, B_6356), k1_relat_1(A_6355)) | r2_hidden('#skF_4'(A_6355, B_6356), B_6356) | k2_relat_1(A_6355)=B_6356 | ~v1_funct_1(A_6355) | ~v1_relat_1(A_6355))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.30  tff(c_41166, plain, (![B_6356]: (r2_hidden('#skF_3'('#skF_8', B_6356), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_6356), B_6356) | k2_relat_1('#skF_8')=B_6356 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_41143])).
% 27.93/17.30  tff(c_41202, plain, (![B_6358]: (r2_hidden('#skF_3'('#skF_8', B_6358), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_6358), B_6358) | k2_relat_1('#skF_8')=B_6358)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_41166])).
% 27.93/17.30  tff(c_41257, plain, (![B_6360]: (~r1_tarski(B_6360, '#skF_4'('#skF_8', B_6360)) | r2_hidden('#skF_3'('#skF_8', B_6360), '#skF_6') | k2_relat_1('#skF_8')=B_6360)), inference(resolution, [status(thm)], [c_41202, c_52])).
% 27.93/17.30  tff(c_41273, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1(k1_xboole_0)), '#skF_6') | k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_806, c_41257])).
% 27.93/17.30  tff(c_41275, plain, (k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_41273])).
% 27.93/17.30  tff(c_41284, plain, (![B_212]: (r1_tarski(k2_relat_1('#skF_8'), B_212))), inference(demodulation, [status(thm), theory('equality')], [c_41275, c_806])).
% 27.93/17.30  tff(c_41335, plain, (![C_19, A_16]: (r2_hidden(C_19, A_16) | ~r2_hidden(C_19, k2_relat_1('#skF_8')) | ~v5_relat_1(k1_xboole_0, A_16) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_41275, c_30])).
% 27.93/17.30  tff(c_41786, plain, (![C_6379, A_6380]: (r2_hidden(C_6379, A_6380) | ~r2_hidden(C_6379, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_324, c_41335])).
% 27.93/17.30  tff(c_41811, plain, (![D_60, A_6380]: (r2_hidden(k1_funct_1('#skF_8', D_60), A_6380) | ~r2_hidden(D_60, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_34, c_41786])).
% 27.93/17.30  tff(c_42086, plain, (![D_6391, A_6392]: (r2_hidden(k1_funct_1('#skF_8', D_6391), A_6392) | ~r2_hidden(D_6391, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_41811])).
% 27.93/17.30  tff(c_42117, plain, (![A_6393, D_6394]: (~r1_tarski(A_6393, k1_funct_1('#skF_8', D_6394)) | ~r2_hidden(D_6394, '#skF_6'))), inference(resolution, [status(thm)], [c_42086, c_52])).
% 27.93/17.30  tff(c_42147, plain, (![D_6395]: (~r2_hidden(D_6395, '#skF_6'))), inference(resolution, [status(thm)], [c_41284, c_42117])).
% 27.93/17.30  tff(c_42185, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_42147])).
% 27.93/17.30  tff(c_42194, plain, (![B_6396]: (r1_tarski('#skF_6', B_6396))), inference(resolution, [status(thm)], [c_6, c_42147])).
% 27.93/17.30  tff(c_41283, plain, (![B_213]: (k2_relat_1('#skF_8')=B_213 | ~r1_tarski(B_213, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_41275, c_41275, c_866])).
% 27.93/17.30  tff(c_42243, plain, (k2_relat_1('#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_42194, c_41283])).
% 27.93/17.30  tff(c_42298, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42243, c_256])).
% 27.93/17.30  tff(c_43029, plain, (![A_6421, C_6422, B_6423, A_6424]: (m1_subset_1(A_6421, k1_zfmisc_1(k2_zfmisc_1(C_6422, B_6423))) | ~r1_tarski(k2_relat_1(A_6421), B_6423) | ~r1_tarski(A_6421, k2_zfmisc_1(C_6422, A_6424)))), inference(resolution, [status(thm)], [c_22, c_31667])).
% 27.93/17.30  tff(c_43031, plain, (![B_6423]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_6423))) | ~r1_tarski(k2_relat_1('#skF_8'), B_6423))), inference(resolution, [status(thm)], [c_42298, c_43029])).
% 27.93/17.30  tff(c_43059, plain, (![B_6425]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_6425))))), inference(demodulation, [status(thm), theory('equality')], [c_42185, c_42243, c_43031])).
% 27.93/17.30  tff(c_43070, plain, (![B_6425]: (k1_relset_1('#skF_6', B_6425, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_43059, c_58])).
% 27.93/17.30  tff(c_43089, plain, (![B_6425]: (k1_relset_1('#skF_6', B_6425, '#skF_8')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_43070])).
% 27.93/17.30  tff(c_43094, plain, (![B_6425]: (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', B_6425)))), inference(resolution, [status(thm)], [c_43059, c_20])).
% 27.93/17.30  tff(c_41115, plain, (![B_6350, C_6351, A_6352]: (k1_xboole_0=B_6350 | v1_funct_2(C_6351, A_6352, B_6350) | k1_relset_1(A_6352, B_6350, C_6351)!=A_6352 | ~m1_subset_1(C_6351, k1_zfmisc_1(k2_zfmisc_1(A_6352, B_6350))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 27.93/17.30  tff(c_43247, plain, (![B_6434, A_6435, A_6436]: (k1_xboole_0=B_6434 | v1_funct_2(A_6435, A_6436, B_6434) | k1_relset_1(A_6436, B_6434, A_6435)!=A_6436 | ~r1_tarski(A_6435, k2_zfmisc_1(A_6436, B_6434)))), inference(resolution, [status(thm)], [c_22, c_41115])).
% 27.93/17.30  tff(c_43250, plain, (![B_6425]: (k1_xboole_0=B_6425 | v1_funct_2('#skF_8', '#skF_6', B_6425) | k1_relset_1('#skF_6', B_6425, '#skF_8')!='#skF_6')), inference(resolution, [status(thm)], [c_43094, c_43247])).
% 27.93/17.30  tff(c_43287, plain, (![B_6437]: (k1_xboole_0=B_6437 | v1_funct_2('#skF_8', '#skF_6', B_6437))), inference(demodulation, [status(thm), theory('equality')], [c_43089, c_43250])).
% 27.93/17.30  tff(c_43298, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_43287, c_167])).
% 27.93/17.30  tff(c_32241, plain, (v5_relat_1(k2_relat_1('#skF_8'), k1_xboole_0) | ~r1_tarski('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_32234])).
% 27.93/17.30  tff(c_41131, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_32241])).
% 27.93/17.30  tff(c_43308, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_43298, c_41131])).
% 27.93/17.30  tff(c_43350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_43308])).
% 27.93/17.30  tff(c_43352, plain, (k2_relat_1(k1_xboole_0)!=k2_relat_1('#skF_8')), inference(splitRight, [status(thm)], [c_41273])).
% 27.93/17.30  tff(c_45323, plain, (![A_6538, C_6539, B_6540, A_6541]: (m1_subset_1(A_6538, k1_zfmisc_1(k2_zfmisc_1(C_6539, B_6540))) | ~r1_tarski(k2_relat_1(A_6538), B_6540) | ~r1_tarski(A_6538, k2_zfmisc_1(C_6539, A_6541)))), inference(resolution, [status(thm)], [c_22, c_31667])).
% 27.93/17.30  tff(c_45460, plain, (![B_6548]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_6548))) | ~r1_tarski(k2_relat_1('#skF_8'), B_6548))), inference(resolution, [status(thm)], [c_256, c_45323])).
% 27.93/17.30  tff(c_45471, plain, (![B_6548]: (k1_relset_1('#skF_6', B_6548, '#skF_8')=k1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), B_6548))), inference(resolution, [status(thm)], [c_45460, c_58])).
% 27.93/17.30  tff(c_45559, plain, (![B_6550]: (k1_relset_1('#skF_6', B_6550, '#skF_8')='#skF_6' | ~r1_tarski(k2_relat_1('#skF_8'), B_6550))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_45471])).
% 27.93/17.30  tff(c_45588, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_31647, c_45559])).
% 27.93/17.30  tff(c_45727, plain, (![B_6556]: (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', B_6556)) | ~r1_tarski(k2_relat_1('#skF_8'), B_6556))), inference(resolution, [status(thm)], [c_45460, c_20])).
% 27.93/17.30  tff(c_45756, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_31647, c_45727])).
% 27.93/17.30  tff(c_46103, plain, (![B_6572, A_6573, A_6574]: (k1_xboole_0=B_6572 | v1_funct_2(A_6573, A_6574, B_6572) | k1_relset_1(A_6574, B_6572, A_6573)!=A_6574 | ~r1_tarski(A_6573, k2_zfmisc_1(A_6574, B_6572)))), inference(resolution, [status(thm)], [c_22, c_41115])).
% 27.93/17.30  tff(c_46112, plain, (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', '#skF_6', '#skF_7') | k1_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_6'), inference(resolution, [status(thm)], [c_45756, c_46103])).
% 27.93/17.30  tff(c_46170, plain, (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_45588, c_46112])).
% 27.93/17.30  tff(c_46171, plain, (k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_167, c_46170])).
% 27.93/17.30  tff(c_44189, plain, (![D_6488, A_6489, B_6490]: (m1_subset_1(D_6488, k1_zfmisc_1(k2_zfmisc_1(A_6489, B_6490))) | ~r1_tarski(k2_relat_1(D_6488), B_6490) | ~m1_subset_1(D_6488, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_31667])).
% 27.93/17.30  tff(c_44223, plain, (![D_6491, A_6492, B_6493]: (r1_tarski(D_6491, k2_zfmisc_1(A_6492, B_6493)) | ~r1_tarski(k2_relat_1(D_6491), B_6493) | ~m1_subset_1(D_6491, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_44189, c_20])).
% 27.93/17.30  tff(c_44252, plain, (![A_6492]: (r1_tarski('#skF_8', k2_zfmisc_1(A_6492, '#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_31647, c_44223])).
% 27.93/17.30  tff(c_44314, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_44252])).
% 27.93/17.30  tff(c_45484, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_45460])).
% 27.93/17.30  tff(c_45494, plain, (~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_44314, c_45484])).
% 27.93/17.30  tff(c_45503, plain, (~v5_relat_1('#skF_8', k1_xboole_0) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_26, c_45494])).
% 27.93/17.30  tff(c_45510, plain, (~v5_relat_1('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_45503])).
% 27.93/17.30  tff(c_46199, plain, (~v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_46171, c_45510])).
% 27.93/17.30  tff(c_46300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31659, c_46199])).
% 27.93/17.30  tff(c_46302, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_44252])).
% 27.93/17.30  tff(c_271, plain, (![C_122, B_9]: (v5_relat_1(C_122, B_9) | ~m1_subset_1(C_122, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_264])).
% 27.93/17.30  tff(c_46327, plain, (![B_6575]: (v5_relat_1('#skF_8', B_6575))), inference(resolution, [status(thm)], [c_46302, c_271])).
% 27.93/17.30  tff(c_850, plain, (![B_116]: (k2_relat_1(k1_xboole_0)=k2_relat_1(B_116) | ~v5_relat_1(B_116, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_808, c_229])).
% 27.93/17.30  tff(c_46342, plain, (k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_46327, c_850])).
% 27.93/17.30  tff(c_46371, plain, (k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_46342])).
% 27.93/17.30  tff(c_46373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43352, c_46371])).
% 27.93/17.30  tff(c_46375, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_32241])).
% 27.93/17.30  tff(c_31205, plain, (![A_5913, B_5914]: (r1_tarski(k2_relat_1(A_5913), B_5914) | ~v1_relat_1(A_5913) | ~r1_tarski(A_5913, k1_xboole_0))), inference(resolution, [status(thm)], [c_286, c_780])).
% 27.93/17.30  tff(c_31255, plain, (![A_5913]: (k2_relat_1(k1_xboole_0)=k2_relat_1(A_5913) | ~v1_relat_1(A_5913) | ~r1_tarski(A_5913, k1_xboole_0))), inference(resolution, [status(thm)], [c_31205, c_866])).
% 27.93/17.30  tff(c_46378, plain, (k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_46375, c_31255])).
% 27.93/17.30  tff(c_46389, plain, (k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_41114, c_46378])).
% 27.93/17.30  tff(c_46407, plain, (![B_212]: (r1_tarski(k2_relat_1('#skF_7'), B_212))), inference(demodulation, [status(thm), theory('equality')], [c_46389, c_806])).
% 27.93/17.30  tff(c_46602, plain, (![A_6577, B_6578]: (r2_hidden('#skF_3'(A_6577, B_6578), k1_relat_1(A_6577)) | r2_hidden('#skF_4'(A_6577, B_6578), B_6578) | k2_relat_1(A_6577)=B_6578 | ~v1_funct_1(A_6577) | ~v1_relat_1(A_6577))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.30  tff(c_46625, plain, (![B_6578]: (r2_hidden('#skF_3'('#skF_8', B_6578), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_6578), B_6578) | k2_relat_1('#skF_8')=B_6578 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_46602])).
% 27.93/17.30  tff(c_46704, plain, (![B_6582]: (r2_hidden('#skF_3'('#skF_8', B_6582), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_6582), B_6582) | k2_relat_1('#skF_8')=B_6582)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_46625])).
% 27.93/17.30  tff(c_47146, plain, (![B_6606]: (~r1_tarski(B_6606, '#skF_4'('#skF_8', B_6606)) | r2_hidden('#skF_3'('#skF_8', B_6606), '#skF_6') | k2_relat_1('#skF_8')=B_6606)), inference(resolution, [status(thm)], [c_46704, c_52])).
% 27.93/17.30  tff(c_47159, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1('#skF_7')), '#skF_6') | k2_relat_1('#skF_7')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_46407, c_47146])).
% 27.93/17.30  tff(c_47724, plain, (k2_relat_1('#skF_7')=k2_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_47159])).
% 27.93/17.30  tff(c_47737, plain, (![B_212]: (r1_tarski(k2_relat_1('#skF_8'), B_212))), inference(demodulation, [status(thm), theory('equality')], [c_47724, c_46407])).
% 27.93/17.30  tff(c_47976, plain, (![A_6633, C_6634, B_6635, A_6636]: (m1_subset_1(A_6633, k1_zfmisc_1(k2_zfmisc_1(C_6634, B_6635))) | ~r1_tarski(k2_relat_1(A_6633), B_6635) | ~r1_tarski(A_6633, k2_zfmisc_1(C_6634, A_6636)))), inference(resolution, [status(thm)], [c_22, c_31667])).
% 27.93/17.30  tff(c_47984, plain, (![B_6635]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_6635))) | ~r1_tarski(k2_relat_1('#skF_8'), B_6635))), inference(resolution, [status(thm)], [c_256, c_47976])).
% 27.93/17.30  tff(c_48926, plain, (![B_6650]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_6650))))), inference(demodulation, [status(thm), theory('equality')], [c_47737, c_47984])).
% 27.93/17.30  tff(c_48937, plain, (![B_6650]: (k1_relset_1('#skF_6', B_6650, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_48926, c_58])).
% 27.93/17.30  tff(c_48956, plain, (![B_6650]: (k1_relset_1('#skF_6', B_6650, '#skF_8')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_48937])).
% 27.93/17.30  tff(c_48961, plain, (![B_6650]: (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', B_6650)))), inference(resolution, [status(thm)], [c_48926, c_20])).
% 27.93/17.30  tff(c_49199, plain, (![B_6666, A_6667, A_6668]: (k1_xboole_0=B_6666 | v1_funct_2(A_6667, A_6668, B_6666) | k1_relset_1(A_6668, B_6666, A_6667)!=A_6668 | ~r1_tarski(A_6667, k2_zfmisc_1(A_6668, B_6666)))), inference(resolution, [status(thm)], [c_22, c_41115])).
% 27.93/17.30  tff(c_49202, plain, (![B_6650]: (k1_xboole_0=B_6650 | v1_funct_2('#skF_8', '#skF_6', B_6650) | k1_relset_1('#skF_6', B_6650, '#skF_8')!='#skF_6')), inference(resolution, [status(thm)], [c_48961, c_49199])).
% 27.93/17.30  tff(c_49252, plain, (![B_6670]: (k1_xboole_0=B_6670 | v1_funct_2('#skF_8', '#skF_6', B_6670))), inference(demodulation, [status(thm), theory('equality')], [c_48956, c_49202])).
% 27.93/17.30  tff(c_49263, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_49252, c_167])).
% 27.93/17.30  tff(c_46395, plain, (k1_xboole_0='#skF_7' | ~r1_tarski(k1_xboole_0, '#skF_7')), inference(resolution, [status(thm)], [c_46375, c_8])).
% 27.93/17.30  tff(c_46792, plain, (~r1_tarski(k1_xboole_0, '#skF_7')), inference(splitLeft, [status(thm)], [c_46395])).
% 27.93/17.30  tff(c_49277, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_49263, c_46792])).
% 27.93/17.30  tff(c_49321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_49277])).
% 27.93/17.30  tff(c_49323, plain, (k2_relat_1('#skF_7')!=k2_relat_1('#skF_8')), inference(splitRight, [status(thm)], [c_47159])).
% 27.93/17.30  tff(c_49335, plain, (![A_6671, C_6672, B_6673, A_6674]: (m1_subset_1(A_6671, k1_zfmisc_1(k2_zfmisc_1(C_6672, B_6673))) | ~r1_tarski(k2_relat_1(A_6671), B_6673) | ~r1_tarski(A_6671, k2_zfmisc_1(C_6672, A_6674)))), inference(resolution, [status(thm)], [c_22, c_31667])).
% 27.93/17.30  tff(c_49419, plain, (![B_6677]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_6677))) | ~r1_tarski(k2_relat_1('#skF_8'), B_6677))), inference(resolution, [status(thm)], [c_256, c_49335])).
% 27.93/17.30  tff(c_49443, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_49419])).
% 27.93/17.30  tff(c_49488, plain, (~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_49443])).
% 27.93/17.30  tff(c_49491, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_32072, c_49488])).
% 27.93/17.30  tff(c_49501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46375, c_49491])).
% 27.93/17.30  tff(c_49502, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_49443])).
% 27.93/17.30  tff(c_49550, plain, (![B_6680]: (v5_relat_1('#skF_8', B_6680))), inference(resolution, [status(thm)], [c_49502, c_271])).
% 27.93/17.30  tff(c_46402, plain, (![B_116]: (k2_relat_1(B_116)=k2_relat_1('#skF_7') | ~v5_relat_1(B_116, k2_relat_1('#skF_7')) | ~v1_relat_1(B_116))), inference(demodulation, [status(thm), theory('equality')], [c_46389, c_46389, c_850])).
% 27.93/17.30  tff(c_49554, plain, (k2_relat_1('#skF_7')=k2_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_49550, c_46402])).
% 27.93/17.30  tff(c_49581, plain, (k2_relat_1('#skF_7')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_49554])).
% 27.93/17.30  tff(c_49583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49323, c_49581])).
% 27.93/17.30  tff(c_49584, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_46395])).
% 27.93/17.30  tff(c_49627, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_49584, c_49584, c_16])).
% 27.93/17.30  tff(c_50340, plain, (![A_6723, C_6724, B_6725, A_6726]: (m1_subset_1(A_6723, k1_zfmisc_1(k2_zfmisc_1(C_6724, B_6725))) | ~r1_tarski(k2_relat_1(A_6723), B_6725) | ~r1_tarski(A_6723, k2_zfmisc_1(C_6724, A_6726)))), inference(resolution, [status(thm)], [c_22, c_31667])).
% 27.93/17.30  tff(c_50368, plain, (![B_6727]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_6727))) | ~r1_tarski(k2_relat_1('#skF_8'), B_6727))), inference(resolution, [status(thm)], [c_256, c_50340])).
% 27.93/17.30  tff(c_50386, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7')) | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_49627, c_50368])).
% 27.93/17.30  tff(c_50395, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_31647, c_50386])).
% 27.93/17.30  tff(c_49620, plain, (![C_122, B_9]: (v5_relat_1(C_122, B_9) | ~m1_subset_1(C_122, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_49584, c_271])).
% 27.93/17.30  tff(c_50411, plain, (![B_6729]: (v5_relat_1('#skF_8', B_6729))), inference(resolution, [status(thm)], [c_50395, c_49620])).
% 27.93/17.30  tff(c_50419, plain, (![B_95]: (r1_tarski(k2_relat_1('#skF_8'), B_95) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_50411, c_228])).
% 27.93/17.30  tff(c_50464, plain, (![B_6730]: (r1_tarski(k2_relat_1('#skF_8'), B_6730))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_50419])).
% 27.93/17.30  tff(c_31111, plain, (![A_5902, D_5903]: (~r1_tarski(k2_relat_1(A_5902), k1_funct_1(A_5902, D_5903)) | ~r2_hidden(D_5903, k1_relat_1(A_5902)) | ~v1_funct_1(A_5902) | ~v1_relat_1(A_5902))), inference(resolution, [status(thm)], [c_31101, c_52])).
% 27.93/17.30  tff(c_50471, plain, (![D_5903]: (~r2_hidden(D_5903, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_50464, c_31111])).
% 27.93/17.30  tff(c_50566, plain, (![D_6732]: (~r2_hidden(D_6732, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_50471])).
% 27.93/17.30  tff(c_50613, plain, (![B_6733]: (r1_tarski('#skF_6', B_6733))), inference(resolution, [status(thm)], [c_6, c_50566])).
% 27.93/17.30  tff(c_46406, plain, (![B_213]: (k2_relat_1('#skF_7')=B_213 | ~r1_tarski(B_213, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_46389, c_46389, c_866])).
% 27.93/17.30  tff(c_50655, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_50613, c_46406])).
% 27.93/17.30  tff(c_592, plain, (![B_185, B_186, A_187]: (v5_relat_1(k2_relat_1(B_185), B_186) | ~v5_relat_1(B_185, k2_zfmisc_1(A_187, B_186)) | ~v1_relat_1(B_185))), inference(resolution, [status(thm)], [c_26, c_289])).
% 27.93/17.30  tff(c_595, plain, (![B_186]: (v5_relat_1(k2_relat_1(k1_xboole_0), B_186) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_324, c_592])).
% 27.93/17.30  tff(c_613, plain, (![B_188]: (v5_relat_1(k2_relat_1(k1_xboole_0), B_188))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_595])).
% 27.93/17.30  tff(c_312, plain, (![B_13, B_131, A_132]: (v5_relat_1(k2_relat_1(B_13), B_131) | ~v5_relat_1(B_13, k2_zfmisc_1(A_132, B_131)) | ~v1_relat_1(B_13))), inference(resolution, [status(thm)], [c_26, c_289])).
% 27.93/17.30  tff(c_621, plain, (![B_131]: (v5_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)), B_131) | ~v1_relat_1(k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_613, c_312])).
% 27.93/17.30  tff(c_673, plain, (~v1_relat_1(k2_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_621])).
% 27.93/17.30  tff(c_46409, plain, (~v1_relat_1(k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_46389, c_673])).
% 27.93/17.30  tff(c_50677, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50655, c_46409])).
% 27.93/17.30  tff(c_50604, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_50566])).
% 27.93/17.30  tff(c_54954, plain, (![C_6935, A_6936, B_6937]: (m1_subset_1(k2_zfmisc_1(C_6935, A_6936), k1_zfmisc_1(k2_zfmisc_1(C_6935, B_6937))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(C_6935, A_6936)), B_6937))), inference(resolution, [status(thm)], [c_12, c_50340])).
% 27.93/17.30  tff(c_54977, plain, (![A_8, B_6937]: (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_8, B_6937))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(A_8, '#skF_7')), B_6937))), inference(superposition, [status(thm), theory('equality')], [c_49627, c_54954])).
% 27.93/17.30  tff(c_54993, plain, (![A_6938, B_6939]: (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_6938, B_6939))))), inference(demodulation, [status(thm), theory('equality')], [c_50604, c_50655, c_49627, c_54977])).
% 27.93/17.30  tff(c_55021, plain, (![A_6938, B_6939]: (r1_tarski('#skF_7', k2_zfmisc_1(A_6938, B_6939)))), inference(resolution, [status(thm)], [c_54993, c_20])).
% 27.93/17.30  tff(c_31292, plain, (![B_5916]: (k2_relat_1(k1_xboole_0)=k2_relat_1(B_5916) | ~v5_relat_1(B_5916, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(B_5916))), inference(resolution, [status(thm)], [c_808, c_229])).
% 27.93/17.30  tff(c_31316, plain, (![A_132]: (k2_relat_1(k2_zfmisc_1(A_132, k2_relat_1(k1_xboole_0)))=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1(A_132, k2_relat_1(k1_xboole_0))))), inference(resolution, [status(thm)], [c_313, c_31292])).
% 27.93/17.30  tff(c_31335, plain, (![A_132]: (k2_relat_1(k2_zfmisc_1(A_132, k2_relat_1(k1_xboole_0)))=k2_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_31316])).
% 27.93/17.30  tff(c_46401, plain, (![A_132]: (k2_relat_1(k2_zfmisc_1(A_132, k2_relat_1('#skF_7')))=k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_46389, c_46389, c_31335])).
% 27.93/17.30  tff(c_50671, plain, (![A_132]: (k2_relat_1(k2_zfmisc_1(A_132, '#skF_6'))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50655, c_50655, c_46401])).
% 27.93/17.30  tff(c_50997, plain, (![A_6742]: (k2_relat_1(k2_zfmisc_1(A_6742, '#skF_6'))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50655, c_50655, c_46401])).
% 27.93/17.30  tff(c_51037, plain, (![A_6742]: (r1_tarski(k2_zfmisc_1(A_6742, '#skF_6'), k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_6742, '#skF_6')), '#skF_6')) | ~v1_relat_1(k2_zfmisc_1(A_6742, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_50997, c_32])).
% 27.93/17.30  tff(c_52685, plain, (![A_6844]: (r1_tarski(k2_zfmisc_1(A_6844, '#skF_6'), k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_6844, '#skF_6')), '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_51037])).
% 27.93/17.30  tff(c_31675, plain, (![A_10, C_5935, B_5936, A_5937]: (m1_subset_1(A_10, k1_zfmisc_1(k2_zfmisc_1(C_5935, B_5936))) | ~r1_tarski(k2_relat_1(A_10), B_5936) | ~r1_tarski(A_10, k2_zfmisc_1(C_5935, A_5937)))), inference(resolution, [status(thm)], [c_22, c_31667])).
% 27.93/17.30  tff(c_52693, plain, (![A_6844, B_5936]: (m1_subset_1(k2_zfmisc_1(A_6844, '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_6844, '#skF_6')), B_5936))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(A_6844, '#skF_6')), B_5936))), inference(resolution, [status(thm)], [c_52685, c_31675])).
% 27.93/17.30  tff(c_54051, plain, (![A_6893, B_6894]: (m1_subset_1(k2_zfmisc_1(A_6893, '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_6893, '#skF_6')), B_6894))))), inference(demodulation, [status(thm), theory('equality')], [c_50604, c_50671, c_52693])).
% 27.93/17.30  tff(c_54088, plain, (![A_6895]: (m1_subset_1(k2_zfmisc_1(A_6895, '#skF_6'), k1_zfmisc_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_49627, c_54051])).
% 27.93/17.30  tff(c_54117, plain, (![A_6901]: (r1_tarski(k2_zfmisc_1(A_6901, '#skF_6'), '#skF_7'))), inference(resolution, [status(thm)], [c_54088, c_20])).
% 27.93/17.30  tff(c_54141, plain, (![A_6901]: (k2_zfmisc_1(A_6901, '#skF_6')='#skF_7' | ~r1_tarski('#skF_7', k2_zfmisc_1(A_6901, '#skF_6')))), inference(resolution, [status(thm)], [c_54117, c_8])).
% 27.93/17.30  tff(c_55098, plain, (![A_6942]: (k2_zfmisc_1(A_6942, '#skF_6')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_55021, c_54141])).
% 27.93/17.30  tff(c_49624, plain, (![B_9, A_8]: (B_9='#skF_7' | A_8='#skF_7' | k2_zfmisc_1(A_8, B_9)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_49584, c_49584, c_49584, c_14])).
% 27.93/17.30  tff(c_55199, plain, (![A_6942]: ('#skF_7'='#skF_6' | A_6942='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_55098, c_49624])).
% 27.93/17.30  tff(c_55212, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_55199])).
% 27.93/17.30  tff(c_50524, plain, (![D_5903]: (~r2_hidden(D_5903, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_50471])).
% 27.93/17.30  tff(c_46634, plain, (![B_6578]: (r2_hidden('#skF_3'('#skF_8', B_6578), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_6578), B_6578) | k2_relat_1('#skF_8')=B_6578)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_46625])).
% 27.93/17.30  tff(c_50807, plain, (![B_6737]: (r2_hidden('#skF_4'('#skF_8', B_6737), B_6737) | k2_relat_1('#skF_8')=B_6737)), inference(negUnitSimplification, [status(thm)], [c_50524, c_46634])).
% 27.93/17.30  tff(c_50826, plain, (k2_relat_1('#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_50807, c_50524])).
% 27.93/17.30  tff(c_31660, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_31647, c_8])).
% 27.93/17.30  tff(c_31666, plain, (~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_31660])).
% 27.93/17.30  tff(c_50840, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50826, c_31666])).
% 27.93/17.30  tff(c_55256, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_55212, c_50840])).
% 27.93/17.30  tff(c_55288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50604, c_55256])).
% 27.93/17.30  tff(c_55688, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_55199])).
% 27.93/17.30  tff(c_55689, plain, (v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_55688, c_41114])).
% 27.93/17.30  tff(c_55842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50677, c_55689])).
% 27.93/17.30  tff(c_55843, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_31660])).
% 27.93/17.30  tff(c_549, plain, (![A_10, A_169]: (v4_relat_1(k2_relat_1(A_10), A_169) | ~v1_relat_1(A_10) | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_286, c_524])).
% 27.93/17.30  tff(c_55887, plain, (![A_169]: (v4_relat_1('#skF_7', A_169) | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_55843, c_549])).
% 27.93/17.30  tff(c_55929, plain, (![A_169]: (v4_relat_1('#skF_7', A_169) | ~r1_tarski('#skF_8', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_55887])).
% 27.93/17.30  tff(c_56007, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_55929])).
% 27.93/17.30  tff(c_55850, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_55843, c_478])).
% 27.93/17.30  tff(c_55853, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_55843, c_256])).
% 27.93/17.30  tff(c_56162, plain, (![B_10324, C_10325, A_10326]: (k1_xboole_0=B_10324 | v1_funct_2(C_10325, A_10326, B_10324) | k1_relset_1(A_10326, B_10324, C_10325)!=A_10326 | ~m1_subset_1(C_10325, k1_zfmisc_1(k2_zfmisc_1(A_10326, B_10324))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 27.93/17.30  tff(c_58510, plain, (![B_10452, A_10453, A_10454]: (k1_xboole_0=B_10452 | v1_funct_2(A_10453, A_10454, B_10452) | k1_relset_1(A_10454, B_10452, A_10453)!=A_10454 | ~r1_tarski(A_10453, k2_zfmisc_1(A_10454, B_10452)))), inference(resolution, [status(thm)], [c_22, c_56162])).
% 27.93/17.30  tff(c_58530, plain, (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', '#skF_6', '#skF_7') | k1_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_6'), inference(resolution, [status(thm)], [c_55853, c_58510])).
% 27.93/17.30  tff(c_58564, plain, (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_55850, c_58530])).
% 27.93/17.30  tff(c_58565, plain, (k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_167, c_58564])).
% 27.93/17.30  tff(c_55905, plain, (![A_12]: (v5_relat_1('#skF_8', A_12) | ~r1_tarski('#skF_7', A_12) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_55843, c_24])).
% 27.93/17.30  tff(c_56015, plain, (![A_10312]: (v5_relat_1('#skF_8', A_10312) | ~r1_tarski('#skF_7', A_10312))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_55905])).
% 27.93/17.30  tff(c_55890, plain, (![A_8]: (v4_relat_1('#skF_7', A_8) | ~v5_relat_1('#skF_8', k1_xboole_0) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_55843, c_542])).
% 27.93/17.30  tff(c_55931, plain, (![A_8]: (v4_relat_1('#skF_7', A_8) | ~v5_relat_1('#skF_8', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_55890])).
% 27.93/17.30  tff(c_56009, plain, (~v5_relat_1('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_55931])).
% 27.93/17.30  tff(c_56046, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_56015, c_56009])).
% 27.93/17.30  tff(c_58624, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58565, c_56046])).
% 27.93/17.30  tff(c_58670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_58624])).
% 27.93/17.30  tff(c_58672, plain, (v5_relat_1('#skF_8', k1_xboole_0)), inference(splitRight, [status(thm)], [c_55931])).
% 27.93/17.30  tff(c_55899, plain, (![A_12]: (r1_tarski('#skF_7', A_12) | ~v5_relat_1('#skF_8', A_12) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_55843, c_26])).
% 27.93/17.30  tff(c_55937, plain, (![A_12]: (r1_tarski('#skF_7', A_12) | ~v5_relat_1('#skF_8', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_55899])).
% 27.93/17.30  tff(c_58679, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_58672, c_55937])).
% 27.93/17.30  tff(c_55944, plain, (![D_10304, C_10305, B_10306, A_10307]: (m1_subset_1(D_10304, k1_zfmisc_1(k2_zfmisc_1(C_10305, B_10306))) | ~r1_tarski(k2_relat_1(D_10304), B_10306) | ~m1_subset_1(D_10304, k1_zfmisc_1(k2_zfmisc_1(C_10305, A_10307))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 27.93/17.30  tff(c_60574, plain, (![A_10563, C_10564, B_10565, A_10566]: (m1_subset_1(A_10563, k1_zfmisc_1(k2_zfmisc_1(C_10564, B_10565))) | ~r1_tarski(k2_relat_1(A_10563), B_10565) | ~r1_tarski(A_10563, k2_zfmisc_1(C_10564, A_10566)))), inference(resolution, [status(thm)], [c_22, c_55944])).
% 27.93/17.30  tff(c_60579, plain, (![B_10565]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_10565))) | ~r1_tarski(k2_relat_1('#skF_8'), B_10565))), inference(resolution, [status(thm)], [c_55853, c_60574])).
% 27.93/17.30  tff(c_60607, plain, (![B_10567]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_10567))) | ~r1_tarski('#skF_7', B_10567))), inference(demodulation, [status(thm), theory('equality')], [c_55843, c_60579])).
% 27.93/17.30  tff(c_60631, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_60607])).
% 27.93/17.30  tff(c_60643, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_58679, c_60631])).
% 27.93/17.30  tff(c_60656, plain, (r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_60643, c_20])).
% 27.93/17.30  tff(c_60667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56007, c_60656])).
% 27.93/17.30  tff(c_60669, plain, (r1_tarski('#skF_8', k1_xboole_0)), inference(splitRight, [status(thm)], [c_55929])).
% 27.93/17.30  tff(c_60674, plain, (k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60669, c_31255])).
% 27.93/17.30  tff(c_60685, plain, (k2_relat_1(k1_xboole_0)='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_55843, c_60674])).
% 27.93/17.30  tff(c_412, plain, (![B_153, D_154]: (~r1_tarski(B_153, k1_funct_1('#skF_8', D_154)) | ~r1_tarski('#skF_7', B_153) | ~r2_hidden(D_154, '#skF_6'))), inference(resolution, [status(thm)], [c_330, c_52])).
% 27.93/17.30  tff(c_735, plain, (![B_207, D_208]: (~r1_tarski('#skF_7', k2_relat_1(B_207)) | ~r2_hidden(D_208, '#skF_6') | ~v5_relat_1(B_207, k1_funct_1('#skF_8', D_208)) | ~v1_relat_1(B_207))), inference(resolution, [status(thm)], [c_26, c_412])).
% 27.93/17.30  tff(c_755, plain, (![D_208]: (~r1_tarski('#skF_7', k2_relat_1(k1_xboole_0)) | ~r2_hidden(D_208, '#skF_6') | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_324, c_735])).
% 27.93/17.30  tff(c_770, plain, (![D_208]: (~r1_tarski('#skF_7', k2_relat_1(k1_xboole_0)) | ~r2_hidden(D_208, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_755])).
% 27.93/17.30  tff(c_775, plain, (~r1_tarski('#skF_7', k2_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_770])).
% 27.93/17.30  tff(c_60701, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60685, c_775])).
% 27.93/17.30  tff(c_60707, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_60701])).
% 27.93/17.30  tff(c_60709, plain, (r1_tarski('#skF_7', k2_relat_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_770])).
% 27.93/17.30  tff(c_60786, plain, (k2_relat_1(k1_xboole_0)='#skF_7' | ~v5_relat_1(k1_xboole_0, '#skF_7') | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_60709, c_229])).
% 27.93/17.30  tff(c_60791, plain, (k2_relat_1(k1_xboole_0)='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_324, c_60786])).
% 27.93/17.30  tff(c_60824, plain, (![A_12]: (r1_tarski('#skF_7', A_12) | ~v5_relat_1(k1_xboole_0, A_12) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_60791, c_26])).
% 27.93/17.30  tff(c_60850, plain, (![A_12]: (r1_tarski('#skF_7', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_324, c_60824])).
% 27.93/17.30  tff(c_60710, plain, (![D_10569]: (~r2_hidden(D_10569, '#skF_6'))), inference(splitRight, [status(thm)], [c_770])).
% 27.93/17.30  tff(c_60721, plain, (![B_10570]: (r1_tarski('#skF_6', B_10570))), inference(resolution, [status(thm)], [c_6, c_60710])).
% 27.93/17.30  tff(c_60934, plain, (![B_10580]: (B_10580='#skF_6' | ~r1_tarski(B_10580, '#skF_6'))), inference(resolution, [status(thm)], [c_60721, c_8])).
% 27.93/17.30  tff(c_60951, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_60850, c_60934])).
% 27.93/17.30  tff(c_60794, plain, (~v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60791, c_673])).
% 27.93/17.30  tff(c_60960, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60951, c_60794])).
% 27.93/17.30  tff(c_60720, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_60710])).
% 27.93/17.30  tff(c_60708, plain, (![D_208]: (~r2_hidden(D_208, '#skF_6'))), inference(splitRight, [status(thm)], [c_770])).
% 27.93/17.30  tff(c_61123, plain, (![A_10591, C_10592]: (r2_hidden('#skF_5'(A_10591, k2_relat_1(A_10591), C_10592), k1_relat_1(A_10591)) | ~r2_hidden(C_10592, k2_relat_1(A_10591)) | ~v1_funct_1(A_10591) | ~v1_relat_1(A_10591))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.30  tff(c_61134, plain, (![C_10592]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_10592), '#skF_6') | ~r2_hidden(C_10592, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_61123])).
% 27.93/17.30  tff(c_61140, plain, (![C_10592]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_10592), '#skF_6') | ~r2_hidden(C_10592, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_61134])).
% 27.93/17.30  tff(c_61142, plain, (![C_10593]: (~r2_hidden(C_10593, k2_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_60708, c_61140])).
% 27.93/17.30  tff(c_61160, plain, (![B_10594]: (r1_tarski(k2_relat_1('#skF_8'), B_10594))), inference(resolution, [status(thm)], [c_6, c_61142])).
% 27.93/17.30  tff(c_60763, plain, (![B_10570]: (B_10570='#skF_6' | ~r1_tarski(B_10570, '#skF_6'))), inference(resolution, [status(thm)], [c_60721, c_8])).
% 27.93/17.30  tff(c_61205, plain, (k2_relat_1('#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_61160, c_60763])).
% 27.93/17.30  tff(c_61106, plain, (![D_10587, C_10588, B_10589, A_10590]: (m1_subset_1(D_10587, k1_zfmisc_1(k2_zfmisc_1(C_10588, B_10589))) | ~r1_tarski(k2_relat_1(D_10587), B_10589) | ~m1_subset_1(D_10587, k1_zfmisc_1(k2_zfmisc_1(C_10588, A_10590))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 27.93/17.30  tff(c_62950, plain, (![D_10689, A_10690, B_10691]: (m1_subset_1(D_10689, k1_zfmisc_1(k2_zfmisc_1(A_10690, B_10691))) | ~r1_tarski(k2_relat_1(D_10689), B_10691) | ~m1_subset_1(D_10689, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_61106])).
% 27.93/17.30  tff(c_62984, plain, (![D_10692, A_10693, B_10694]: (r1_tarski(D_10692, k2_zfmisc_1(A_10693, B_10694)) | ~r1_tarski(k2_relat_1(D_10692), B_10694) | ~m1_subset_1(D_10692, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_62950, c_20])).
% 27.93/17.30  tff(c_62992, plain, (![A_10693, B_10694]: (r1_tarski('#skF_8', k2_zfmisc_1(A_10693, B_10694)) | ~r1_tarski('#skF_6', B_10694) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_61205, c_62984])).
% 27.93/17.30  tff(c_63008, plain, (![A_10693, B_10694]: (r1_tarski('#skF_8', k2_zfmisc_1(A_10693, B_10694)) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_60720, c_62992])).
% 27.93/17.30  tff(c_63065, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_63008])).
% 27.93/17.30  tff(c_61240, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_61205, c_256])).
% 27.93/17.30  tff(c_64424, plain, (![A_10748, C_10749, B_10750, A_10751]: (m1_subset_1(A_10748, k1_zfmisc_1(k2_zfmisc_1(C_10749, B_10750))) | ~r1_tarski(k2_relat_1(A_10748), B_10750) | ~r1_tarski(A_10748, k2_zfmisc_1(C_10749, A_10751)))), inference(resolution, [status(thm)], [c_22, c_61106])).
% 27.93/17.30  tff(c_64453, plain, (![B_10750]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_10750))) | ~r1_tarski(k2_relat_1('#skF_8'), B_10750))), inference(resolution, [status(thm)], [c_61240, c_64424])).
% 27.93/17.30  tff(c_64491, plain, (![B_10752]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_10752))))), inference(demodulation, [status(thm), theory('equality')], [c_60720, c_61205, c_64453])).
% 27.93/17.30  tff(c_64514, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_64491])).
% 27.93/17.30  tff(c_64528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63065, c_64514])).
% 27.93/17.30  tff(c_64575, plain, (![A_10754, B_10755]: (r1_tarski('#skF_8', k2_zfmisc_1(A_10754, B_10755)))), inference(splitRight, [status(thm)], [c_63008])).
% 27.93/17.30  tff(c_64578, plain, (![A_10754, B_10755]: (k1_relset_1(A_10754, B_10755, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_64575, c_386])).
% 27.93/17.30  tff(c_64592, plain, (![A_10754, B_10755]: (k1_relset_1(A_10754, B_10755, '#skF_8')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_64578])).
% 27.93/17.30  tff(c_64530, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_63008])).
% 27.93/17.30  tff(c_64544, plain, (![B_74]: (v1_funct_2('#skF_8', k1_xboole_0, B_74) | k1_relset_1(k1_xboole_0, B_74, '#skF_8')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_64530, c_85])).
% 27.93/17.30  tff(c_64686, plain, (![B_74]: (v1_funct_2('#skF_8', k1_xboole_0, B_74) | k1_xboole_0!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64592, c_64544])).
% 27.93/17.30  tff(c_64687, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_64686])).
% 27.93/17.30  tff(c_64529, plain, (![A_10693, B_10694]: (r1_tarski('#skF_8', k2_zfmisc_1(A_10693, B_10694)))), inference(splitRight, [status(thm)], [c_63008])).
% 27.93/17.30  tff(c_64708, plain, (![A_10766, C_10767, B_10768, A_10769]: (m1_subset_1(A_10766, k1_zfmisc_1(k2_zfmisc_1(C_10767, B_10768))) | ~r1_tarski(k2_relat_1(A_10766), B_10768) | ~r1_tarski(A_10766, k2_zfmisc_1(C_10767, A_10769)))), inference(resolution, [status(thm)], [c_22, c_61106])).
% 27.93/17.30  tff(c_64710, plain, (![A_10693, B_10768]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_10693, B_10768))) | ~r1_tarski(k2_relat_1('#skF_8'), B_10768))), inference(resolution, [status(thm)], [c_64529, c_64708])).
% 27.93/17.30  tff(c_64756, plain, (![A_10770, B_10771]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_10770, B_10771))))), inference(demodulation, [status(thm), theory('equality')], [c_60720, c_61205, c_64710])).
% 27.93/17.30  tff(c_64762, plain, (![B_10771, A_10770]: (k1_xboole_0=B_10771 | v1_funct_2('#skF_8', A_10770, B_10771) | k1_relset_1(A_10770, B_10771, '#skF_8')!=A_10770)), inference(resolution, [status(thm)], [c_64756, c_68])).
% 27.93/17.30  tff(c_64884, plain, (![B_10779, A_10780]: (k1_xboole_0=B_10779 | v1_funct_2('#skF_8', A_10780, B_10779) | A_10780!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64592, c_64762])).
% 27.93/17.30  tff(c_60962, plain, (~v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60951, c_167])).
% 27.93/17.30  tff(c_64890, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_64884, c_60962])).
% 27.93/17.30  tff(c_64901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64687, c_64890])).
% 27.93/17.30  tff(c_64903, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_64686])).
% 27.93/17.30  tff(c_64552, plain, (r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_64530, c_20])).
% 27.93/17.30  tff(c_64573, plain, (k1_xboole_0='#skF_8' | ~r1_tarski(k1_xboole_0, '#skF_8')), inference(resolution, [status(thm)], [c_64552, c_8])).
% 27.93/17.30  tff(c_64682, plain, (~r1_tarski(k1_xboole_0, '#skF_8')), inference(splitLeft, [status(thm)], [c_64573])).
% 27.93/17.30  tff(c_64904, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_64903, c_64682])).
% 27.93/17.30  tff(c_64955, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60720, c_64904])).
% 27.93/17.30  tff(c_64956, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_64573])).
% 27.93/17.30  tff(c_60961, plain, (k2_relat_1(k1_xboole_0)='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_60951, c_60791])).
% 27.93/17.30  tff(c_60973, plain, (![D_60]: (r2_hidden(k1_funct_1(k1_xboole_0, D_60), '#skF_6') | ~r2_hidden(D_60, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_60961, c_34])).
% 27.93/17.30  tff(c_61009, plain, (![D_60]: (r2_hidden(k1_funct_1(k1_xboole_0, D_60), '#skF_6') | ~r2_hidden(D_60, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_60973])).
% 27.93/17.30  tff(c_61010, plain, (![D_60]: (~r2_hidden(D_60, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_60708, c_61009])).
% 27.93/17.30  tff(c_61360, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_61010])).
% 27.93/17.30  tff(c_64980, plain, (~v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_64956, c_61360])).
% 27.93/17.30  tff(c_65013, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_64980])).
% 27.93/17.30  tff(c_65016, plain, (![D_10781]: (~r2_hidden(D_10781, k1_relat_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_61010])).
% 27.93/17.30  tff(c_65047, plain, (![B_10785]: (r1_tarski(k1_relat_1(k1_xboole_0), B_10785))), inference(resolution, [status(thm)], [c_6, c_65016])).
% 27.93/17.30  tff(c_65089, plain, (k1_relat_1(k1_xboole_0)='#skF_6'), inference(resolution, [status(thm)], [c_65047, c_60763])).
% 27.93/17.30  tff(c_60774, plain, (![C_10572, B_10573]: (v1_funct_2(C_10572, k1_xboole_0, B_10573) | k1_relset_1(k1_xboole_0, B_10573, C_10572)!=k1_xboole_0 | ~m1_subset_1(C_10572, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_66])).
% 27.93/17.30  tff(c_60776, plain, (![B_10573]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_10573) | k1_relset_1(k1_xboole_0, B_10573, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_347, c_60774])).
% 27.93/17.30  tff(c_60781, plain, (![B_10573]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_10573) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_393, c_60776])).
% 27.93/17.30  tff(c_65182, plain, (![B_10573]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_10573) | k1_xboole_0!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_65089, c_60781])).
% 27.93/17.30  tff(c_65183, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_65182])).
% 27.93/17.30  tff(c_67674, plain, (![A_10907, C_10908, B_10909, A_10910]: (m1_subset_1(A_10907, k1_zfmisc_1(k2_zfmisc_1(C_10908, B_10909))) | ~r1_tarski(k2_relat_1(A_10907), B_10909) | ~r1_tarski(A_10907, k2_zfmisc_1(C_10908, A_10910)))), inference(resolution, [status(thm)], [c_22, c_61106])).
% 27.93/17.30  tff(c_67695, plain, (![B_10909]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_10909))) | ~r1_tarski(k2_relat_1('#skF_8'), B_10909))), inference(resolution, [status(thm)], [c_61240, c_67674])).
% 27.93/17.30  tff(c_67730, plain, (![B_10911]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_10911))))), inference(demodulation, [status(thm), theory('equality')], [c_60720, c_61205, c_67695])).
% 27.93/17.30  tff(c_67741, plain, (![B_10911]: (k1_relset_1('#skF_6', B_10911, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_67730, c_58])).
% 27.93/17.30  tff(c_67760, plain, (![B_10911]: (k1_relset_1('#skF_6', B_10911, '#skF_8')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_67741])).
% 27.93/17.30  tff(c_67765, plain, (![B_10911]: (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', B_10911)))), inference(resolution, [status(thm)], [c_67730, c_20])).
% 27.93/17.30  tff(c_61321, plain, (![B_10596, C_10597, A_10598]: (k1_xboole_0=B_10596 | v1_funct_2(C_10597, A_10598, B_10596) | k1_relset_1(A_10598, B_10596, C_10597)!=A_10598 | ~m1_subset_1(C_10597, k1_zfmisc_1(k2_zfmisc_1(A_10598, B_10596))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 27.93/17.30  tff(c_68340, plain, (![B_10936, A_10937, A_10938]: (k1_xboole_0=B_10936 | v1_funct_2(A_10937, A_10938, B_10936) | k1_relset_1(A_10938, B_10936, A_10937)!=A_10938 | ~r1_tarski(A_10937, k2_zfmisc_1(A_10938, B_10936)))), inference(resolution, [status(thm)], [c_22, c_61321])).
% 27.93/17.30  tff(c_68346, plain, (![B_10911]: (k1_xboole_0=B_10911 | v1_funct_2('#skF_8', '#skF_6', B_10911) | k1_relset_1('#skF_6', B_10911, '#skF_8')!='#skF_6')), inference(resolution, [status(thm)], [c_67765, c_68340])).
% 27.93/17.30  tff(c_68412, plain, (![B_10939]: (k1_xboole_0=B_10939 | v1_funct_2('#skF_8', '#skF_6', B_10939))), inference(demodulation, [status(thm), theory('equality')], [c_67760, c_68346])).
% 27.93/17.30  tff(c_68415, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_68412, c_60962])).
% 27.93/17.30  tff(c_68422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65183, c_68415])).
% 27.93/17.30  tff(c_68424, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_65182])).
% 27.93/17.30  tff(c_68454, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68424, c_119])).
% 27.93/17.30  tff(c_68461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60960, c_68454])).
% 27.93/17.30  tff(c_68463, plain, (v1_relat_1(k2_relat_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_621])).
% 27.93/17.30  tff(c_608, plain, (![B_186]: (v5_relat_1(k2_relat_1(k1_xboole_0), B_186))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_595])).
% 27.93/17.30  tff(c_91518, plain, (![B_12013]: (r1_tarski(k2_relat_1(k2_relat_1(k1_xboole_0)), B_12013) | ~v1_relat_1(k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_608, c_91498])).
% 27.93/17.30  tff(c_91535, plain, (![B_12013]: (r1_tarski(k2_relat_1(k2_relat_1(k1_xboole_0)), B_12013))), inference(demodulation, [status(thm), theory('equality')], [c_68463, c_91518])).
% 27.93/17.30  tff(c_91765, plain, (![B_12019]: (k2_relat_1(k1_xboole_0)=B_12019 | ~r1_tarski(B_12019, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_91540, c_8])).
% 27.93/17.30  tff(c_91787, plain, (k2_relat_1(k2_relat_1(k1_xboole_0))=k2_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_91535, c_91765])).
% 27.93/17.30  tff(c_91829, plain, (![C_19, A_16]: (r2_hidden(C_19, A_16) | ~r2_hidden(C_19, k2_relat_1(k1_xboole_0)) | ~v5_relat_1(k2_relat_1(k1_xboole_0), A_16) | ~v1_relat_1(k2_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_91787, c_30])).
% 27.93/17.30  tff(c_91898, plain, (![C_12023, A_12024]: (r2_hidden(C_12023, A_12024) | ~r2_hidden(C_12023, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_68463, c_608, c_91829])).
% 27.93/17.30  tff(c_91901, plain, (![D_60, A_12024]: (r2_hidden(k1_funct_1(k1_xboole_0, D_60), A_12024) | ~r2_hidden(D_60, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_91898])).
% 27.93/17.30  tff(c_91913, plain, (![D_60, A_12024]: (r2_hidden(k1_funct_1(k1_xboole_0, D_60), A_12024) | ~r2_hidden(D_60, k1_xboole_0) | ~v1_funct_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_91387, c_91901])).
% 27.93/17.30  tff(c_92398, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_91913])).
% 27.93/17.30  tff(c_99802, plain, (~v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_99786, c_92398])).
% 27.93/17.30  tff(c_99836, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_99802])).
% 27.93/17.30  tff(c_99837, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1(k1_xboole_0)), '#skF_6')), inference(splitRight, [status(thm)], [c_92769])).
% 27.93/17.30  tff(c_102338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102332, c_99837])).
% 27.93/17.30  tff(c_102342, plain, (![D_15465, A_15466]: (r2_hidden(k1_funct_1(k1_xboole_0, D_15465), A_15466) | ~r2_hidden(D_15465, k1_xboole_0))), inference(splitRight, [status(thm)], [c_91913])).
% 27.93/17.30  tff(c_102369, plain, (![A_15467, D_15468]: (~r1_tarski(A_15467, k1_funct_1(k1_xboole_0, D_15468)) | ~r2_hidden(D_15468, k1_xboole_0))), inference(resolution, [status(thm)], [c_102342, c_52])).
% 27.93/17.30  tff(c_102393, plain, (![D_15469]: (~r2_hidden(D_15469, k1_xboole_0))), inference(resolution, [status(thm)], [c_91538, c_102369])).
% 27.93/17.30  tff(c_102408, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_102393])).
% 27.93/17.30  tff(c_102390, plain, (![D_15468]: (~r2_hidden(D_15468, k1_xboole_0))), inference(resolution, [status(thm)], [c_91538, c_102369])).
% 27.93/17.30  tff(c_102340, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_91913])).
% 27.93/17.30  tff(c_102422, plain, (![B_15473]: (r1_tarski(k1_xboole_0, B_15473))), inference(resolution, [status(thm)], [c_6, c_102393])).
% 27.93/17.30  tff(c_102478, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_102422, c_91598])).
% 27.93/17.30  tff(c_102742, plain, (![A_15484, B_15485]: (r2_hidden('#skF_3'(A_15484, B_15485), k1_relat_1(A_15484)) | r2_hidden('#skF_4'(A_15484, B_15485), B_15485) | k2_relat_1(A_15484)=B_15485 | ~v1_funct_1(A_15484) | ~v1_relat_1(A_15484))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.30  tff(c_102762, plain, (![B_15485]: (r2_hidden('#skF_3'(k1_xboole_0, B_15485), k1_xboole_0) | r2_hidden('#skF_4'(k1_xboole_0, B_15485), B_15485) | k2_relat_1(k1_xboole_0)=B_15485 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_91387, c_102742])).
% 27.93/17.30  tff(c_102772, plain, (![B_15485]: (r2_hidden('#skF_3'(k1_xboole_0, B_15485), k1_xboole_0) | r2_hidden('#skF_4'(k1_xboole_0, B_15485), B_15485) | k1_xboole_0=B_15485)), inference(demodulation, [status(thm), theory('equality')], [c_119, c_102340, c_102478, c_102762])).
% 27.93/17.30  tff(c_102776, plain, (![B_15486]: (r2_hidden('#skF_4'(k1_xboole_0, B_15486), B_15486) | k1_xboole_0=B_15486)), inference(negUnitSimplification, [status(thm)], [c_102390, c_102772])).
% 27.93/17.30  tff(c_92288, plain, (![C_12042]: (r2_hidden(C_12042, '#skF_7') | ~r2_hidden(C_12042, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_92279, c_91645])).
% 27.93/17.30  tff(c_102795, plain, (r2_hidden('#skF_4'(k1_xboole_0, k2_relat_1('#skF_8')), '#skF_7') | k2_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_102776, c_92288])).
% 27.93/17.30  tff(c_103003, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_102795])).
% 27.93/17.30  tff(c_103014, plain, (~r1_tarski(k2_zfmisc_1('#skF_6', k1_xboole_0), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_103003, c_287])).
% 27.93/17.30  tff(c_103021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102408, c_16, c_103014])).
% 27.93/17.30  tff(c_103023, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_102795])).
% 27.93/17.30  tff(c_102765, plain, (![B_15485]: (r2_hidden('#skF_3'('#skF_8', B_15485), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_15485), B_15485) | k2_relat_1('#skF_8')=B_15485 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_102742])).
% 27.93/17.30  tff(c_102816, plain, (![B_15488]: (r2_hidden('#skF_3'('#skF_8', B_15488), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_15488), B_15488) | k2_relat_1('#skF_8')=B_15488)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_102765])).
% 27.93/17.30  tff(c_103256, plain, (![B_15518]: (~r1_tarski(B_15518, '#skF_4'('#skF_8', B_15518)) | r2_hidden('#skF_3'('#skF_8', B_15518), '#skF_6') | k2_relat_1('#skF_8')=B_15518)), inference(resolution, [status(thm)], [c_102816, c_52])).
% 27.93/17.30  tff(c_103262, plain, (r2_hidden('#skF_3'('#skF_8', k1_xboole_0), '#skF_6') | k2_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_102408, c_103256])).
% 27.93/17.30  tff(c_103272, plain, (r2_hidden('#skF_3'('#skF_8', k1_xboole_0), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_103023, c_103262])).
% 27.93/17.30  tff(c_105327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105321, c_103272])).
% 27.93/17.30  tff(c_105328, plain, (k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8'))='#skF_8'), inference(splitRight, [status(thm)], [c_263])).
% 27.93/17.30  tff(c_137096, plain, (k2_zfmisc_1('#skF_6', '#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_137059, c_105328])).
% 27.93/17.30  tff(c_137003, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_136965])).
% 27.93/17.30  tff(c_105395, plain, (![A_15613, B_15612]: (v5_relat_1(k2_zfmisc_1(A_15613, B_15612), B_15612))), inference(resolution, [status(thm)], [c_12, c_105372])).
% 27.93/17.30  tff(c_117688, plain, (![B_20996]: (k2_relat_1(k1_xboole_0)=k2_relat_1(B_20996) | ~v5_relat_1(B_20996, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(B_20996))), inference(resolution, [status(thm)], [c_117452, c_229])).
% 27.93/17.30  tff(c_117712, plain, (![A_15613]: (k2_relat_1(k2_zfmisc_1(A_15613, k2_relat_1(k1_xboole_0)))=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1(A_15613, k2_relat_1(k1_xboole_0))))), inference(resolution, [status(thm)], [c_105395, c_117688])).
% 27.93/17.30  tff(c_117731, plain, (![A_15613]: (k2_relat_1(k2_zfmisc_1(A_15613, k2_relat_1(k1_xboole_0)))=k2_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_117712])).
% 27.93/17.30  tff(c_136167, plain, (![A_15613]: (k2_relat_1(k2_zfmisc_1(A_15613, k2_relat_1('#skF_8')))=k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_136164, c_136164, c_117731])).
% 27.93/17.30  tff(c_137076, plain, (![A_15613]: (k2_relat_1(k2_zfmisc_1(A_15613, '#skF_6'))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_137059, c_137059, c_136167])).
% 27.93/17.30  tff(c_137582, plain, (![A_21810]: (k2_relat_1(k2_zfmisc_1(A_21810, '#skF_6'))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_137059, c_137059, c_136167])).
% 27.93/17.30  tff(c_137660, plain, (![A_21810]: (r1_tarski(k2_zfmisc_1(A_21810, '#skF_6'), k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21810, '#skF_6')), '#skF_6')) | ~v1_relat_1(k2_zfmisc_1(A_21810, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_137582, c_32])).
% 27.93/17.30  tff(c_138947, plain, (![A_21883]: (r1_tarski(k2_zfmisc_1(A_21883, '#skF_6'), k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21883, '#skF_6')), '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_137660])).
% 27.93/17.30  tff(c_118055, plain, (![A_10, C_21009, B_21010, A_21011]: (m1_subset_1(A_10, k1_zfmisc_1(k2_zfmisc_1(C_21009, B_21010))) | ~r1_tarski(k2_relat_1(A_10), B_21010) | ~r1_tarski(A_10, k2_zfmisc_1(C_21009, A_21011)))), inference(resolution, [status(thm)], [c_22, c_118045])).
% 27.93/17.30  tff(c_138955, plain, (![A_21883, B_21010]: (m1_subset_1(k2_zfmisc_1(A_21883, '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21883, '#skF_6')), B_21010))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(A_21883, '#skF_6')), B_21010))), inference(resolution, [status(thm)], [c_138947, c_118055])).
% 27.93/17.30  tff(c_140732, plain, (![A_21939, B_21940]: (m1_subset_1(k2_zfmisc_1(A_21939, '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21939, '#skF_6')), B_21940))))), inference(demodulation, [status(thm), theory('equality')], [c_137003, c_137076, c_138955])).
% 27.93/17.30  tff(c_140755, plain, (![B_21940]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1('#skF_6', '#skF_6')), B_21940))))), inference(superposition, [status(thm), theory('equality')], [c_137096, c_140732])).
% 27.93/17.30  tff(c_140953, plain, (![B_21950]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_21950))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_137096, c_140755])).
% 27.93/17.30  tff(c_140964, plain, (![B_21950]: (k1_relset_1('#skF_6', B_21950, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_140953, c_58])).
% 27.93/17.30  tff(c_140985, plain, (![B_21950]: (k1_relset_1('#skF_6', B_21950, '#skF_8')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_140964])).
% 27.93/17.30  tff(c_141148, plain, (![B_21955]: (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', B_21955)))), inference(resolution, [status(thm)], [c_140953, c_20])).
% 27.93/17.30  tff(c_141154, plain, (![B_21955]: (k1_xboole_0=B_21955 | v1_funct_2('#skF_8', '#skF_6', B_21955) | k1_relset_1('#skF_6', B_21955, '#skF_8')!='#skF_6')), inference(resolution, [status(thm)], [c_141148, c_118224])).
% 27.93/17.30  tff(c_141193, plain, (![B_21956]: (k1_xboole_0=B_21956 | v1_funct_2('#skF_8', '#skF_6', B_21956))), inference(demodulation, [status(thm), theory('equality')], [c_140985, c_141154])).
% 27.93/17.30  tff(c_141205, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_141193, c_167])).
% 27.93/17.30  tff(c_118483, plain, (![B_21050, B_21051]: (r2_hidden('#skF_1'(k2_relat_1('#skF_8'), B_21050), B_21051) | ~r1_tarski('#skF_7', B_21051) | r1_tarski(k2_relat_1('#skF_8'), B_21050))), inference(resolution, [status(thm)], [c_118014, c_2])).
% 27.93/17.30  tff(c_118520, plain, (![B_21054]: (~r1_tarski('#skF_7', B_21054) | r1_tarski(k2_relat_1('#skF_8'), B_21054))), inference(resolution, [status(thm)], [c_118483, c_4])).
% 27.93/17.30  tff(c_118658, plain, (![B_21056, A_21057]: (v5_relat_1(k2_relat_1('#skF_8'), B_21056) | ~r1_tarski('#skF_7', k2_zfmisc_1(A_21057, B_21056)))), inference(resolution, [status(thm)], [c_118520, c_275])).
% 27.93/17.30  tff(c_118665, plain, (![B_9]: (v5_relat_1(k2_relat_1('#skF_8'), B_9) | ~r1_tarski('#skF_7', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_118658])).
% 27.93/17.30  tff(c_135901, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_118665])).
% 27.93/17.30  tff(c_141230, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_141205, c_135901])).
% 27.93/17.30  tff(c_141271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_141230])).
% 27.93/17.30  tff(c_141272, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1(k1_xboole_0)), '#skF_6')), inference(splitRight, [status(thm)], [c_136108])).
% 27.93/17.30  tff(c_144048, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144041, c_141272])).
% 27.93/17.30  tff(c_144050, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_118665])).
% 27.93/17.30  tff(c_118508, plain, (![B_21051]: (~r1_tarski('#skF_7', B_21051) | r1_tarski(k2_relat_1('#skF_8'), B_21051))), inference(resolution, [status(thm)], [c_118483, c_4])).
% 27.93/17.30  tff(c_145095, plain, (![D_22115, A_22116, B_22117]: (m1_subset_1(D_22115, k1_zfmisc_1(k2_zfmisc_1(A_22116, B_22117))) | ~r1_tarski(k2_relat_1(D_22115), B_22117) | ~m1_subset_1(D_22115, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_118045])).
% 27.93/17.30  tff(c_152051, plain, (![D_22374, A_22375, B_22376]: (r1_tarski(D_22374, k2_zfmisc_1(A_22375, B_22376)) | ~r1_tarski(k2_relat_1(D_22374), B_22376) | ~m1_subset_1(D_22374, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_145095, c_20])).
% 27.93/17.30  tff(c_152090, plain, (![A_22375]: (r1_tarski('#skF_8', k2_zfmisc_1(A_22375, '#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_118025, c_152051])).
% 27.93/17.30  tff(c_152387, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_152090])).
% 27.93/17.30  tff(c_150455, plain, (![A_22304, C_22305, B_22306, A_22307]: (m1_subset_1(A_22304, k1_zfmisc_1(k2_zfmisc_1(C_22305, B_22306))) | ~r1_tarski(k2_relat_1(A_22304), B_22306) | ~r1_tarski(A_22304, k2_zfmisc_1(C_22305, A_22307)))), inference(resolution, [status(thm)], [c_22, c_118045])).
% 27.93/17.30  tff(c_154748, plain, (![A_22497, B_22498]: (m1_subset_1(A_22497, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_22497), B_22498))) | ~r1_tarski(k2_relat_1(A_22497), B_22498) | ~v1_relat_1(A_22497))), inference(resolution, [status(thm)], [c_32, c_150455])).
% 27.93/17.30  tff(c_154778, plain, (![B_22498]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_22498))) | ~r1_tarski(k2_relat_1('#skF_8'), B_22498) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_154748])).
% 27.93/17.30  tff(c_154907, plain, (![B_22501]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_22501))) | ~r1_tarski(k2_relat_1('#skF_8'), B_22501))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_154778])).
% 27.93/17.30  tff(c_154934, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_154907])).
% 27.93/17.30  tff(c_154946, plain, (~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_152387, c_154934])).
% 27.93/17.30  tff(c_154970, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_118508, c_154946])).
% 27.93/17.30  tff(c_154980, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144050, c_154970])).
% 27.93/17.30  tff(c_154982, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_152090])).
% 27.93/17.30  tff(c_154995, plain, (r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_154982, c_20])).
% 27.93/17.30  tff(c_155006, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150873, c_154995])).
% 27.93/17.30  tff(c_155007, plain, (![D_22320]: (~r2_hidden(D_22320, '#skF_6'))), inference(splitRight, [status(thm)], [c_150872])).
% 27.93/17.30  tff(c_105347, plain, (k2_relat_1('#skF_8')=k1_xboole_0 | k1_xboole_0='#skF_6' | k1_xboole_0!='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_105328, c_14])).
% 27.93/17.30  tff(c_105358, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_105347])).
% 27.93/17.30  tff(c_144071, plain, (![A_22076, B_22077]: (r2_hidden('#skF_3'(A_22076, B_22077), k1_relat_1(A_22076)) | r2_hidden('#skF_4'(A_22076, B_22077), B_22077) | k2_relat_1(A_22076)=B_22077 | ~v1_funct_1(A_22076) | ~v1_relat_1(A_22076))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.30  tff(c_144095, plain, (![B_22077]: (r2_hidden('#skF_3'('#skF_8', B_22077), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_22077), B_22077) | k2_relat_1('#skF_8')=B_22077 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_144071])).
% 27.93/17.30  tff(c_144104, plain, (![B_22077]: (r2_hidden('#skF_3'('#skF_8', B_22077), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_22077), B_22077) | k2_relat_1('#skF_8')=B_22077)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_144095])).
% 27.93/17.30  tff(c_118668, plain, (v5_relat_1(k2_relat_1('#skF_8'), k2_relat_1('#skF_7')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_118658])).
% 27.93/17.30  tff(c_118669, plain, (~v1_relat_1('#skF_7')), inference(splitLeft, [status(thm)], [c_118668])).
% 27.93/17.30  tff(c_133195, plain, (![A_21626, D_21627]: (~r1_tarski(k2_relat_1(A_21626), k1_funct_1(A_21626, D_21627)) | ~r2_hidden(D_21627, k1_relat_1(A_21626)) | ~v1_funct_1(A_21626) | ~v1_relat_1(A_21626))), inference(resolution, [status(thm)], [c_117387, c_52])).
% 27.93/17.30  tff(c_133231, plain, (![D_21628, A_21629]: (~r2_hidden(D_21628, k1_relat_1(A_21629)) | ~v1_funct_1(A_21629) | ~v1_relat_1(A_21629) | ~r1_tarski(A_21629, k1_xboole_0))), inference(resolution, [status(thm)], [c_117451, c_133195])).
% 27.93/17.30  tff(c_133287, plain, (![D_21628]: (~r2_hidden(D_21628, '#skF_6') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_78, c_133231])).
% 27.93/17.30  tff(c_133304, plain, (![D_21628]: (~r2_hidden(D_21628, '#skF_6') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_133287])).
% 27.93/17.30  tff(c_133305, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_133304])).
% 27.93/17.30  tff(c_133553, plain, (![D_21636, A_21637, B_21638]: (m1_subset_1(D_21636, k1_zfmisc_1(k2_zfmisc_1(A_21637, B_21638))) | ~r1_tarski(k2_relat_1(D_21636), B_21638) | ~m1_subset_1(D_21636, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_118045])).
% 27.93/17.30  tff(c_134318, plain, (![D_21672, A_21673, B_21674]: (r1_tarski(D_21672, k2_zfmisc_1(A_21673, B_21674)) | ~r1_tarski(k2_relat_1(D_21672), B_21674) | ~m1_subset_1(D_21672, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_133553, c_20])).
% 27.93/17.30  tff(c_134350, plain, (![A_21673]: (r1_tarski('#skF_8', k2_zfmisc_1(A_21673, '#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_118025, c_134318])).
% 27.93/17.30  tff(c_134689, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_134350])).
% 27.93/17.30  tff(c_124867, plain, (![A_21303, D_21304]: (~r1_tarski(k2_relat_1(A_21303), k1_funct_1(A_21303, D_21304)) | ~r2_hidden(D_21304, k1_relat_1(A_21303)) | ~v1_funct_1(A_21303) | ~v1_relat_1(A_21303))), inference(resolution, [status(thm)], [c_117387, c_52])).
% 27.93/17.30  tff(c_124913, plain, (![D_21305, A_21306]: (~r2_hidden(D_21305, k1_relat_1(A_21306)) | ~v1_funct_1(A_21306) | ~v1_relat_1(A_21306) | ~r1_tarski(A_21306, k1_xboole_0))), inference(resolution, [status(thm)], [c_117451, c_124867])).
% 27.93/17.30  tff(c_124977, plain, (![D_21305]: (~r2_hidden(D_21305, '#skF_6') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_78, c_124913])).
% 27.93/17.30  tff(c_124996, plain, (![D_21305]: (~r2_hidden(D_21305, '#skF_6') | ~r1_tarski('#skF_8', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_124977])).
% 27.93/17.30  tff(c_124997, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_124996])).
% 27.93/17.30  tff(c_125616, plain, (![A_21334, C_21335, B_21336, A_21337]: (m1_subset_1(A_21334, k1_zfmisc_1(k2_zfmisc_1(C_21335, B_21336))) | ~r1_tarski(k2_relat_1(A_21334), B_21336) | ~r1_tarski(A_21334, k2_zfmisc_1(C_21335, A_21337)))), inference(resolution, [status(thm)], [c_22, c_118045])).
% 27.93/17.30  tff(c_126645, plain, (![A_21386, B_21387]: (m1_subset_1(A_21386, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_21386), B_21387))) | ~r1_tarski(k2_relat_1(A_21386), B_21387) | ~v1_relat_1(A_21386))), inference(resolution, [status(thm)], [c_32, c_125616])).
% 27.93/17.30  tff(c_126675, plain, (![B_21387]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_21387))) | ~r1_tarski(k2_relat_1('#skF_8'), B_21387) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_126645])).
% 27.93/17.30  tff(c_126687, plain, (![B_21388]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_21388))) | ~r1_tarski(k2_relat_1('#skF_8'), B_21388))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_126675])).
% 27.93/17.30  tff(c_126698, plain, (![B_21388]: (k1_relset_1('#skF_6', B_21388, '#skF_8')=k1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), B_21388))), inference(resolution, [status(thm)], [c_126687, c_58])).
% 27.93/17.30  tff(c_126843, plain, (![B_21390]: (k1_relset_1('#skF_6', B_21390, '#skF_8')='#skF_6' | ~r1_tarski(k2_relat_1('#skF_8'), B_21390))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_126698])).
% 27.93/17.30  tff(c_126903, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_118025, c_126843])).
% 27.93/17.30  tff(c_126961, plain, (![B_21394]: (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', B_21394)) | ~r1_tarski(k2_relat_1('#skF_8'), B_21394))), inference(resolution, [status(thm)], [c_126687, c_20])).
% 27.93/17.30  tff(c_127021, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_118025, c_126961])).
% 27.93/17.30  tff(c_127161, plain, (![B_21397, A_21398, A_21399]: (k1_xboole_0=B_21397 | v1_funct_2(A_21398, A_21399, B_21397) | k1_relset_1(A_21399, B_21397, A_21398)!=A_21399 | ~r1_tarski(A_21398, k2_zfmisc_1(A_21399, B_21397)))), inference(resolution, [status(thm)], [c_22, c_118210])).
% 27.93/17.30  tff(c_127167, plain, (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', '#skF_6', '#skF_7') | k1_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_6'), inference(resolution, [status(thm)], [c_127021, c_127161])).
% 27.93/17.30  tff(c_127227, plain, (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_126903, c_127167])).
% 27.93/17.30  tff(c_127228, plain, (k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_167, c_127227])).
% 27.93/17.30  tff(c_125249, plain, (![D_21313, A_21314, B_21315]: (m1_subset_1(D_21313, k1_zfmisc_1(k2_zfmisc_1(A_21314, B_21315))) | ~r1_tarski(k2_relat_1(D_21313), B_21315) | ~m1_subset_1(D_21313, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_118045])).
% 27.93/17.30  tff(c_125471, plain, (![D_21325, A_21326, B_21327]: (r1_tarski(D_21325, k2_zfmisc_1(A_21326, B_21327)) | ~r1_tarski(k2_relat_1(D_21325), B_21327) | ~m1_subset_1(D_21325, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_125249, c_20])).
% 27.93/17.30  tff(c_125509, plain, (![A_21326]: (r1_tarski('#skF_8', k2_zfmisc_1(A_21326, '#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_118025, c_125471])).
% 27.93/17.30  tff(c_125595, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_125509])).
% 27.93/17.30  tff(c_126714, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_126687])).
% 27.93/17.30  tff(c_126726, plain, (~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_125595, c_126714])).
% 27.93/17.30  tff(c_126756, plain, (~v5_relat_1('#skF_8', k1_xboole_0) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_26, c_126726])).
% 27.93/17.30  tff(c_126763, plain, (~v5_relat_1('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_126756])).
% 27.93/17.30  tff(c_127247, plain, (~v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_127228, c_126763])).
% 27.93/17.30  tff(c_127361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118037, c_127247])).
% 27.93/17.30  tff(c_127363, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_125509])).
% 27.93/17.30  tff(c_127376, plain, (r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_127363, c_20])).
% 27.93/17.30  tff(c_127387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124997, c_127376])).
% 27.93/17.30  tff(c_127388, plain, (![D_21305]: (~r2_hidden(D_21305, '#skF_6'))), inference(splitRight, [status(thm)], [c_124996])).
% 27.93/17.30  tff(c_118670, plain, (![A_21058, B_21059]: (r2_hidden('#skF_3'(A_21058, B_21059), k1_relat_1(A_21058)) | r2_hidden('#skF_4'(A_21058, B_21059), B_21059) | k2_relat_1(A_21058)=B_21059 | ~v1_funct_1(A_21058) | ~v1_relat_1(A_21058))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.30  tff(c_118693, plain, (![B_21059]: (r2_hidden('#skF_3'('#skF_8', B_21059), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_21059), B_21059) | k2_relat_1('#skF_8')=B_21059 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_118670])).
% 27.93/17.30  tff(c_118704, plain, (![B_21060]: (r2_hidden('#skF_3'('#skF_8', B_21060), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_21060), B_21060) | k2_relat_1('#skF_8')=B_21060)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_118693])).
% 27.93/17.30  tff(c_118857, plain, (![B_21068]: (~r1_tarski(B_21068, '#skF_4'('#skF_8', B_21068)) | r2_hidden('#skF_3'('#skF_8', B_21068), '#skF_6') | k2_relat_1('#skF_8')=B_21068)), inference(resolution, [status(thm)], [c_118704, c_52])).
% 27.93/17.30  tff(c_118873, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1(k1_xboole_0)), '#skF_6') | k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_117450, c_118857])).
% 27.93/17.30  tff(c_118875, plain, (k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_118873])).
% 27.93/17.30  tff(c_118884, plain, (![B_20983]: (r1_tarski(k2_relat_1('#skF_8'), B_20983))), inference(demodulation, [status(thm), theory('equality')], [c_118875, c_117450])).
% 27.93/17.30  tff(c_119712, plain, (![A_21098, D_21099]: (~r1_tarski(k2_relat_1(A_21098), k1_funct_1(A_21098, D_21099)) | ~r2_hidden(D_21099, k1_relat_1(A_21098)) | ~v1_funct_1(A_21098) | ~v1_relat_1(A_21098))), inference(resolution, [status(thm)], [c_117387, c_52])).
% 27.93/17.30  tff(c_119719, plain, (![D_21099]: (~r2_hidden(D_21099, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_118884, c_119712])).
% 27.93/17.30  tff(c_119750, plain, (![D_21100]: (~r2_hidden(D_21100, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_119719])).
% 27.93/17.30  tff(c_119797, plain, (![B_21101]: (r1_tarski('#skF_6', B_21101))), inference(resolution, [status(thm)], [c_6, c_119750])).
% 27.93/17.30  tff(c_118882, plain, (![B_20984]: (k2_relat_1('#skF_8')=B_20984 | ~r1_tarski(B_20984, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_118875, c_118875, c_117510])).
% 27.93/17.30  tff(c_119844, plain, (k2_relat_1('#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_119797, c_118882])).
% 27.93/17.30  tff(c_119881, plain, (k2_zfmisc_1('#skF_6', '#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_119844, c_105328])).
% 27.93/17.30  tff(c_119788, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_119750])).
% 27.93/17.30  tff(c_118878, plain, (![A_15613]: (k2_relat_1(k2_zfmisc_1(A_15613, k2_relat_1('#skF_8')))=k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_118875, c_118875, c_117731])).
% 27.93/17.30  tff(c_119862, plain, (![A_15613]: (k2_relat_1(k2_zfmisc_1(A_15613, '#skF_6'))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_119844, c_119844, c_118878])).
% 27.93/17.30  tff(c_120391, plain, (![A_21112]: (k2_relat_1(k2_zfmisc_1(A_21112, '#skF_6'))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_119844, c_119844, c_118878])).
% 27.93/17.30  tff(c_120469, plain, (![A_21112]: (r1_tarski(k2_zfmisc_1(A_21112, '#skF_6'), k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21112, '#skF_6')), '#skF_6')) | ~v1_relat_1(k2_zfmisc_1(A_21112, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_120391, c_32])).
% 27.93/17.30  tff(c_121882, plain, (![A_21190]: (r1_tarski(k2_zfmisc_1(A_21190, '#skF_6'), k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21190, '#skF_6')), '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_120469])).
% 27.93/17.30  tff(c_121890, plain, (![A_21190, B_21010]: (m1_subset_1(k2_zfmisc_1(A_21190, '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21190, '#skF_6')), B_21010))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(A_21190, '#skF_6')), B_21010))), inference(resolution, [status(thm)], [c_121882, c_118055])).
% 27.93/17.30  tff(c_123548, plain, (![A_21241, B_21242]: (m1_subset_1(k2_zfmisc_1(A_21241, '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21241, '#skF_6')), B_21242))))), inference(demodulation, [status(thm), theory('equality')], [c_119788, c_119862, c_121890])).
% 27.93/17.30  tff(c_123571, plain, (![B_21242]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1('#skF_6', '#skF_6')), B_21242))))), inference(superposition, [status(thm), theory('equality')], [c_119881, c_123548])).
% 27.93/17.30  tff(c_123883, plain, (![B_21255]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_21255))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_119881, c_123571])).
% 27.93/17.30  tff(c_123894, plain, (![B_21255]: (k1_relset_1('#skF_6', B_21255, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_123883, c_58])).
% 27.93/17.30  tff(c_123915, plain, (![B_21255]: (k1_relset_1('#skF_6', B_21255, '#skF_8')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_123894])).
% 27.93/17.30  tff(c_123964, plain, (![B_21257]: (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', B_21257)))), inference(resolution, [status(thm)], [c_123883, c_20])).
% 27.93/17.30  tff(c_123967, plain, (![B_21257]: (k1_xboole_0=B_21257 | v1_funct_2('#skF_8', '#skF_6', B_21257) | k1_relset_1('#skF_6', B_21257, '#skF_8')!='#skF_6')), inference(resolution, [status(thm)], [c_123964, c_118224])).
% 27.93/17.30  tff(c_124012, plain, (![B_21261]: (k1_xboole_0=B_21261 | v1_funct_2('#skF_8', '#skF_6', B_21261))), inference(demodulation, [status(thm), theory('equality')], [c_123915, c_123967])).
% 27.93/17.30  tff(c_124024, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_124012, c_167])).
% 27.93/17.30  tff(c_118703, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_118665])).
% 27.93/17.30  tff(c_124049, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_124024, c_118703])).
% 27.93/17.30  tff(c_124090, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_124049])).
% 27.93/17.30  tff(c_124091, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1(k1_xboole_0)), '#skF_6')), inference(splitRight, [status(thm)], [c_118873])).
% 27.93/17.30  tff(c_127395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127388, c_124091])).
% 27.93/17.30  tff(c_127397, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_118665])).
% 27.93/17.30  tff(c_134035, plain, (![A_21659, C_21660, B_21661, A_21662]: (m1_subset_1(A_21659, k1_zfmisc_1(k2_zfmisc_1(C_21660, B_21661))) | ~r1_tarski(k2_relat_1(A_21659), B_21661) | ~r1_tarski(A_21659, k2_zfmisc_1(C_21660, A_21662)))), inference(resolution, [status(thm)], [c_22, c_118045])).
% 27.93/17.30  tff(c_135664, plain, (![A_21751, B_21752]: (m1_subset_1(A_21751, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_21751), B_21752))) | ~r1_tarski(k2_relat_1(A_21751), B_21752) | ~v1_relat_1(A_21751))), inference(resolution, [status(thm)], [c_32, c_134035])).
% 27.93/17.30  tff(c_135706, plain, (![A_21753]: (m1_subset_1(A_21753, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(A_21753), k1_xboole_0) | ~v1_relat_1(A_21753))), inference(superposition, [status(thm), theory('equality')], [c_16, c_135664])).
% 27.93/17.30  tff(c_135710, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0)) | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_118508, c_135706])).
% 27.93/17.30  tff(c_135728, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_127397, c_82, c_135710])).
% 27.93/17.30  tff(c_135730, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134689, c_135728])).
% 27.93/17.30  tff(c_135732, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_134350])).
% 27.93/17.30  tff(c_135745, plain, (r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_135732, c_20])).
% 27.93/17.30  tff(c_135756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133305, c_135745])).
% 27.93/17.30  tff(c_135757, plain, (![D_21628]: (~r2_hidden(D_21628, '#skF_6'))), inference(splitRight, [status(thm)], [c_133304])).
% 27.93/17.30  tff(c_127398, plain, (![B_21400]: (r2_hidden('#skF_3'('#skF_8', B_21400), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_21400), B_21400) | k2_relat_1('#skF_8')=B_21400)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_118693])).
% 27.93/17.30  tff(c_127613, plain, (![B_21412]: (~r1_tarski(B_21412, '#skF_4'('#skF_8', B_21412)) | r2_hidden('#skF_3'('#skF_8', B_21412), '#skF_6') | k2_relat_1('#skF_8')=B_21412)), inference(resolution, [status(thm)], [c_127398, c_52])).
% 27.93/17.30  tff(c_127629, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1(k1_xboole_0)), '#skF_6') | k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_117450, c_127613])).
% 27.93/17.30  tff(c_127695, plain, (k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_127629])).
% 27.93/17.30  tff(c_127704, plain, (![B_20983]: (r1_tarski(k2_relat_1('#skF_8'), B_20983))), inference(demodulation, [status(thm), theory('equality')], [c_127695, c_117450])).
% 27.93/17.30  tff(c_128299, plain, (![A_21436, D_21437]: (~r1_tarski(k2_relat_1(A_21436), k1_funct_1(A_21436, D_21437)) | ~r2_hidden(D_21437, k1_relat_1(A_21436)) | ~v1_funct_1(A_21436) | ~v1_relat_1(A_21436))), inference(resolution, [status(thm)], [c_117387, c_52])).
% 27.93/17.30  tff(c_128306, plain, (![D_21437]: (~r2_hidden(D_21437, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_127704, c_128299])).
% 27.93/17.30  tff(c_128337, plain, (![D_21438]: (~r2_hidden(D_21438, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_128306])).
% 27.93/17.30  tff(c_128373, plain, (![B_21439]: (r1_tarski('#skF_6', B_21439))), inference(resolution, [status(thm)], [c_6, c_128337])).
% 27.93/17.30  tff(c_127702, plain, (![B_20984]: (k2_relat_1('#skF_8')=B_20984 | ~r1_tarski(B_20984, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_127695, c_127695, c_117510])).
% 27.93/17.30  tff(c_128422, plain, (k2_relat_1('#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_128373, c_127702])).
% 27.93/17.30  tff(c_128456, plain, (k2_zfmisc_1('#skF_6', '#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_128422, c_105328])).
% 27.93/17.30  tff(c_128366, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_128337])).
% 27.93/17.30  tff(c_127698, plain, (![A_15613]: (k2_relat_1(k2_zfmisc_1(A_15613, k2_relat_1('#skF_8')))=k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_127695, c_127695, c_117731])).
% 27.93/17.30  tff(c_128436, plain, (![A_15613]: (k2_relat_1(k2_zfmisc_1(A_15613, '#skF_6'))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_128422, c_128422, c_127698])).
% 27.93/17.30  tff(c_128899, plain, (![A_21447]: (k2_relat_1(k2_zfmisc_1(A_21447, '#skF_6'))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_128422, c_128422, c_127698])).
% 27.93/17.30  tff(c_128968, plain, (![A_21447]: (r1_tarski(k2_zfmisc_1(A_21447, '#skF_6'), k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21447, '#skF_6')), '#skF_6')) | ~v1_relat_1(k2_zfmisc_1(A_21447, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_128899, c_32])).
% 27.93/17.30  tff(c_130499, plain, (![A_21531]: (r1_tarski(k2_zfmisc_1(A_21531, '#skF_6'), k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21531, '#skF_6')), '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_128968])).
% 27.93/17.30  tff(c_130507, plain, (![A_21531, B_21010]: (m1_subset_1(k2_zfmisc_1(A_21531, '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21531, '#skF_6')), B_21010))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(A_21531, '#skF_6')), B_21010))), inference(resolution, [status(thm)], [c_130499, c_118055])).
% 27.93/17.30  tff(c_131971, plain, (![A_21577, B_21578]: (m1_subset_1(k2_zfmisc_1(A_21577, '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(A_21577, '#skF_6')), B_21578))))), inference(demodulation, [status(thm), theory('equality')], [c_128366, c_128436, c_130507])).
% 27.93/17.30  tff(c_131994, plain, (![B_21578]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_zfmisc_1('#skF_6', '#skF_6')), B_21578))))), inference(superposition, [status(thm), theory('equality')], [c_128456, c_131971])).
% 27.93/17.30  tff(c_132292, plain, (![B_21591]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_21591))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_128456, c_131994])).
% 27.93/17.30  tff(c_132303, plain, (![B_21591]: (k1_relset_1('#skF_6', B_21591, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_132292, c_58])).
% 27.93/17.30  tff(c_132324, plain, (![B_21591]: (k1_relset_1('#skF_6', B_21591, '#skF_8')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_132303])).
% 27.93/17.30  tff(c_132319, plain, (![B_21591]: (k1_xboole_0=B_21591 | v1_funct_2('#skF_8', '#skF_6', B_21591) | k1_relset_1('#skF_6', B_21591, '#skF_8')!='#skF_6')), inference(resolution, [status(thm)], [c_132292, c_68])).
% 27.93/17.30  tff(c_132976, plain, (![B_21616]: (k1_xboole_0=B_21616 | v1_funct_2('#skF_8', '#skF_6', B_21616))), inference(demodulation, [status(thm), theory('equality')], [c_132324, c_132319])).
% 27.93/17.30  tff(c_132988, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_132976, c_167])).
% 27.93/17.30  tff(c_127446, plain, (k1_xboole_0='#skF_7' | ~r1_tarski(k1_xboole_0, '#skF_7')), inference(resolution, [status(thm)], [c_127397, c_8])).
% 27.93/17.30  tff(c_127485, plain, (~r1_tarski(k1_xboole_0, '#skF_7')), inference(splitLeft, [status(thm)], [c_127446])).
% 27.93/17.30  tff(c_133019, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_132988, c_127485])).
% 27.93/17.30  tff(c_133061, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_133019])).
% 27.93/17.30  tff(c_133062, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1(k1_xboole_0)), '#skF_6')), inference(splitRight, [status(thm)], [c_127629])).
% 27.93/17.30  tff(c_135764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135757, c_133062])).
% 27.93/17.30  tff(c_135765, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_127446])).
% 27.93/17.30  tff(c_135863, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_135765, c_119])).
% 27.93/17.30  tff(c_135868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118669, c_135863])).
% 27.93/17.30  tff(c_135870, plain, (v1_relat_1('#skF_7')), inference(splitRight, [status(thm)], [c_118668])).
% 27.93/17.30  tff(c_117601, plain, (![A_20993, B_20994]: (r1_tarski(k2_relat_1(A_20993), B_20994) | ~v1_relat_1(A_20993) | ~r1_tarski(A_20993, k1_xboole_0))), inference(resolution, [status(thm)], [c_286, c_117424])).
% 27.93/17.30  tff(c_117650, plain, (![A_20993]: (k2_relat_1(k1_xboole_0)=k2_relat_1(A_20993) | ~v1_relat_1(A_20993) | ~r1_tarski(A_20993, k1_xboole_0))), inference(resolution, [status(thm)], [c_117601, c_117510])).
% 27.93/17.30  tff(c_144053, plain, (k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_144050, c_117650])).
% 27.93/17.30  tff(c_144064, plain, (k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_135870, c_144053])).
% 27.93/17.30  tff(c_117737, plain, (![A_20997]: (k2_relat_1(k2_zfmisc_1(A_20997, k2_relat_1(k1_xboole_0)))=k2_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_117712])).
% 27.93/17.30  tff(c_117792, plain, (![A_20997, A_12]: (v5_relat_1(k2_zfmisc_1(A_20997, k2_relat_1(k1_xboole_0)), A_12) | ~r1_tarski(k2_relat_1(k1_xboole_0), A_12) | ~v1_relat_1(k2_zfmisc_1(A_20997, k2_relat_1(k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_117737, c_24])).
% 27.93/17.30  tff(c_117834, plain, (![A_20997, A_12]: (v5_relat_1(k2_zfmisc_1(A_20997, k2_relat_1(k1_xboole_0)), A_12))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_117450, c_117792])).
% 27.93/17.30  tff(c_144145, plain, (![A_20997, A_12]: (v5_relat_1(k2_zfmisc_1(A_20997, k2_relat_1('#skF_7')), A_12))), inference(demodulation, [status(thm), theory('equality')], [c_144064, c_117834])).
% 27.93/17.30  tff(c_144629, plain, (![A_22097]: (k2_relat_1(k2_zfmisc_1(A_22097, k2_relat_1('#skF_7')))=k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_144064, c_144064, c_117731])).
% 27.93/17.30  tff(c_144689, plain, (![C_19, A_16, A_22097]: (r2_hidden(C_19, A_16) | ~r2_hidden(C_19, k2_relat_1('#skF_7')) | ~v5_relat_1(k2_zfmisc_1(A_22097, k2_relat_1('#skF_7')), A_16) | ~v1_relat_1(k2_zfmisc_1(A_22097, k2_relat_1('#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_144629, c_30])).
% 27.93/17.30  tff(c_144831, plain, (![C_22104, A_22105]: (r2_hidden(C_22104, A_22105) | ~r2_hidden(C_22104, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_144145, c_144689])).
% 27.93/17.30  tff(c_144858, plain, (![A_22105]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_7')), A_22105) | r2_hidden('#skF_3'('#skF_8', k2_relat_1('#skF_7')), '#skF_6') | k2_relat_1('#skF_7')=k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_144104, c_144831])).
% 27.93/17.30  tff(c_145251, plain, (k2_relat_1('#skF_7')=k2_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_144858])).
% 27.93/17.30  tff(c_144152, plain, (![B_20983]: (r1_tarski(k2_relat_1('#skF_7'), B_20983))), inference(demodulation, [status(thm), theory('equality')], [c_144064, c_117450])).
% 27.93/17.30  tff(c_145428, plain, (![B_22125]: (r1_tarski(k2_relat_1('#skF_8'), B_22125))), inference(demodulation, [status(thm), theory('equality')], [c_145251, c_144152])).
% 27.93/17.30  tff(c_117397, plain, (![A_20977, D_20978]: (~r1_tarski(k2_relat_1(A_20977), k1_funct_1(A_20977, D_20978)) | ~r2_hidden(D_20978, k1_relat_1(A_20977)) | ~v1_funct_1(A_20977) | ~v1_relat_1(A_20977))), inference(resolution, [status(thm)], [c_117387, c_52])).
% 27.93/17.30  tff(c_145432, plain, (![D_20978]: (~r2_hidden(D_20978, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_145428, c_117397])).
% 27.93/17.30  tff(c_145490, plain, (![D_20978]: (~r2_hidden(D_20978, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_145432])).
% 27.93/17.30  tff(c_145726, plain, (![B_22132]: (r2_hidden('#skF_4'('#skF_8', B_22132), B_22132) | k2_relat_1('#skF_8')=B_22132)), inference(negUnitSimplification, [status(thm)], [c_145490, c_144104])).
% 27.93/17.30  tff(c_145745, plain, (k2_relat_1('#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_145726, c_145490])).
% 27.93/17.30  tff(c_145770, plain, (k2_zfmisc_1('#skF_6', '#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_145745, c_105328])).
% 27.93/17.30  tff(c_146071, plain, (![A_22133]: (k2_zfmisc_1(k1_relat_1(A_22133), k2_relat_1(A_22133))=A_22133 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_22133), k2_relat_1(A_22133)), A_22133) | ~v1_relat_1(A_22133))), inference(resolution, [status(thm)], [c_239, c_8])).
% 27.93/17.30  tff(c_146083, plain, (k2_zfmisc_1(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'))='#skF_8' | ~r1_tarski(k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8')), '#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_78, c_146071])).
% 27.93/17.30  tff(c_146091, plain, (k2_zfmisc_1('#skF_6', '#skF_6')='#skF_8' | ~r1_tarski(k2_zfmisc_1('#skF_6', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_145745, c_145745, c_78, c_146083])).
% 27.93/17.30  tff(c_146248, plain, (~r1_tarski(k2_zfmisc_1('#skF_6', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_146091])).
% 27.93/17.30  tff(c_146345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_145770, c_146248])).
% 27.93/17.30  tff(c_146346, plain, (k2_zfmisc_1('#skF_6', '#skF_6')='#skF_8'), inference(splitRight, [status(thm)], [c_146091])).
% 27.93/17.30  tff(c_105417, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_88])).
% 27.93/17.30  tff(c_105420, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_105417])).
% 27.93/17.30  tff(c_105424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_105420])).
% 27.93/17.30  tff(c_105426, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_88])).
% 27.93/17.30  tff(c_145519, plain, (![D_22126]: (~r2_hidden(D_22126, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_145432])).
% 27.93/17.30  tff(c_145562, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_145519])).
% 27.93/17.30  tff(c_145263, plain, (k2_relat_1(k1_xboole_0)=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_145251, c_144064])).
% 27.93/17.30  tff(c_146092, plain, (k2_relat_1(k1_xboole_0)='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_145745, c_145263])).
% 27.93/17.30  tff(c_150025, plain, (![D_22286, A_22287, B_22288]: (r1_tarski(D_22286, k2_zfmisc_1(A_22287, B_22288)) | ~r1_tarski(k2_relat_1(D_22286), B_22288) | ~m1_subset_1(D_22286, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_145095, c_20])).
% 27.93/17.30  tff(c_150033, plain, (![A_22287, B_22288]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_22287, B_22288)) | ~r1_tarski('#skF_6', B_22288) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_146092, c_150025])).
% 27.93/17.30  tff(c_150068, plain, (![A_22289, B_22290]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_22289, B_22290)))), inference(demodulation, [status(thm), theory('equality')], [c_105426, c_145562, c_150033])).
% 27.93/17.30  tff(c_150089, plain, (r1_tarski(k1_xboole_0, '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_146346, c_150068])).
% 27.93/17.30  tff(c_150118, plain, (k1_xboole_0='#skF_8' | ~r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_150089, c_8])).
% 27.93/17.30  tff(c_150129, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_105358, c_150118])).
% 27.93/17.30  tff(c_146417, plain, (![A_22138, C_22139, B_22140, A_22141]: (m1_subset_1(A_22138, k1_zfmisc_1(k2_zfmisc_1(C_22139, B_22140))) | ~r1_tarski(k2_relat_1(A_22138), B_22140) | ~r1_tarski(A_22138, k2_zfmisc_1(C_22139, A_22141)))), inference(resolution, [status(thm)], [c_22, c_118045])).
% 27.93/17.30  tff(c_150213, plain, (![A_22295, B_22296]: (m1_subset_1(A_22295, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_22295), B_22296))) | ~r1_tarski(k2_relat_1(A_22295), B_22296) | ~v1_relat_1(A_22295))), inference(resolution, [status(thm)], [c_32, c_146417])).
% 27.93/17.30  tff(c_150243, plain, (![B_22296]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_22296))) | ~r1_tarski(k2_relat_1('#skF_8'), B_22296) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_150213])).
% 27.93/17.30  tff(c_150255, plain, (![B_22297]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_22297))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_145562, c_145745, c_150243])).
% 27.93/17.30  tff(c_150280, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_150255])).
% 27.93/17.30  tff(c_150331, plain, (r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_150280, c_20])).
% 27.93/17.30  tff(c_150343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150129, c_150331])).
% 27.93/17.30  tff(c_150345, plain, (k2_relat_1('#skF_7')!=k2_relat_1('#skF_8')), inference(splitRight, [status(thm)], [c_144858])).
% 27.93/17.30  tff(c_144294, plain, (![B_22079]: (r2_hidden('#skF_3'('#skF_8', B_22079), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_22079), B_22079) | k2_relat_1('#skF_8')=B_22079)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_144095])).
% 27.93/17.30  tff(c_144609, plain, (![B_22096]: (~r1_tarski(B_22096, '#skF_4'('#skF_8', B_22096)) | r2_hidden('#skF_3'('#skF_8', B_22096), '#skF_6') | k2_relat_1('#skF_8')=B_22096)), inference(resolution, [status(thm)], [c_144294, c_52])).
% 27.93/17.30  tff(c_144622, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1('#skF_7')), '#skF_6') | k2_relat_1('#skF_7')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_144152, c_144609])).
% 27.93/17.30  tff(c_150623, plain, (r2_hidden('#skF_3'('#skF_8', k2_relat_1('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_150345, c_144622])).
% 27.93/17.30  tff(c_155014, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155007, c_150623])).
% 27.93/17.30  tff(c_155016, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_105347])).
% 27.93/17.30  tff(c_155132, plain, (![A_73]: (v1_funct_2('#skF_8', A_73, '#skF_8') | A_73='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_155016, c_155016, c_155016, c_155016, c_155016, c_88])).
% 27.93/17.30  tff(c_155133, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_155132])).
% 27.93/17.30  tff(c_155136, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_22, c_155133])).
% 27.93/17.30  tff(c_155140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_155136])).
% 27.93/17.30  tff(c_155142, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(splitRight, [status(thm)], [c_155132])).
% 27.93/17.30  tff(c_155024, plain, (![B_9]: (k2_zfmisc_1('#skF_8', B_9)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_155016, c_155016, c_18])).
% 27.93/17.30  tff(c_155347, plain, (![A_22543, B_22544, C_22545]: (k1_relset_1(A_22543, B_22544, C_22545)=k1_relat_1(C_22545) | ~m1_subset_1(C_22545, k1_zfmisc_1(k2_zfmisc_1(A_22543, B_22544))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 27.93/17.30  tff(c_155399, plain, (![B_22548, C_22549]: (k1_relset_1('#skF_8', B_22548, C_22549)=k1_relat_1(C_22549) | ~m1_subset_1(C_22549, k1_zfmisc_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_155024, c_155347])).
% 27.93/17.30  tff(c_155401, plain, (![B_22548]: (k1_relset_1('#skF_8', B_22548, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_155142, c_155399])).
% 27.93/17.30  tff(c_155406, plain, (![B_22548]: (k1_relset_1('#skF_8', B_22548, '#skF_8')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_155401])).
% 27.93/17.30  tff(c_155487, plain, (![C_22561, B_22562]: (v1_funct_2(C_22561, '#skF_8', B_22562) | k1_relset_1('#skF_8', B_22562, C_22561)!='#skF_8' | ~m1_subset_1(C_22561, k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_155016, c_155016, c_155016, c_155016, c_85])).
% 27.93/17.30  tff(c_155489, plain, (![B_22562]: (v1_funct_2('#skF_8', '#skF_8', B_22562) | k1_relset_1('#skF_8', B_22562, '#skF_8')!='#skF_8')), inference(resolution, [status(thm)], [c_155142, c_155487])).
% 27.93/17.30  tff(c_155494, plain, (![B_22562]: (v1_funct_2('#skF_8', '#skF_8', B_22562) | '#skF_6'!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_155406, c_155489])).
% 27.93/17.30  tff(c_155496, plain, ('#skF_6'!='#skF_8'), inference(splitLeft, [status(thm)], [c_155494])).
% 27.93/17.30  tff(c_155017, plain, (![A_10, B_127]: (v5_relat_1(A_10, B_127) | ~r1_tarski(A_10, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_155016, c_286])).
% 27.93/17.30  tff(c_155015, plain, (k1_xboole_0='#skF_6' | k2_relat_1('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_105347])).
% 27.93/17.30  tff(c_155102, plain, ('#skF_6'='#skF_8' | k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_155016, c_155016, c_155015])).
% 27.93/17.30  tff(c_155103, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(splitLeft, [status(thm)], [c_155102])).
% 27.93/17.30  tff(c_155112, plain, (![A_12]: (r1_tarski('#skF_8', A_12) | ~v5_relat_1('#skF_8', A_12) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_155103, c_26])).
% 27.93/17.30  tff(c_155160, plain, (![A_22517]: (r1_tarski('#skF_8', A_22517) | ~v5_relat_1('#skF_8', A_22517))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_155112])).
% 27.93/17.30  tff(c_155164, plain, (![B_127]: (r1_tarski('#skF_8', B_127) | ~r1_tarski('#skF_8', '#skF_8'))), inference(resolution, [status(thm)], [c_155017, c_155160])).
% 27.93/17.30  tff(c_155174, plain, (![B_127]: (r1_tarski('#skF_8', B_127))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_155164])).
% 27.93/17.30  tff(c_155810, plain, (![A_22598, D_22599]: (r2_hidden(k1_funct_1(A_22598, D_22599), k2_relat_1(A_22598)) | ~r2_hidden(D_22599, k1_relat_1(A_22598)) | ~v1_funct_1(A_22598) | ~v1_relat_1(A_22598))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.93/17.30  tff(c_155820, plain, (![D_22599]: (r2_hidden(k1_funct_1('#skF_8', D_22599), '#skF_8') | ~r2_hidden(D_22599, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_155103, c_155810])).
% 27.93/17.30  tff(c_155826, plain, (![D_22600]: (r2_hidden(k1_funct_1('#skF_8', D_22600), '#skF_8') | ~r2_hidden(D_22600, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_155820])).
% 27.93/17.30  tff(c_155833, plain, (![D_22600]: (~r1_tarski('#skF_8', k1_funct_1('#skF_8', D_22600)) | ~r2_hidden(D_22600, '#skF_6'))), inference(resolution, [status(thm)], [c_155826, c_52])).
% 27.93/17.30  tff(c_155841, plain, (![D_22601]: (~r2_hidden(D_22601, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_155174, c_155833])).
% 27.93/17.30  tff(c_155852, plain, (![B_22602]: (r1_tarski('#skF_6', B_22602))), inference(resolution, [status(thm)], [c_6, c_155841])).
% 27.93/17.30  tff(c_155181, plain, (![B_22518]: (r1_tarski('#skF_8', B_22518))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_155164])).
% 27.93/17.30  tff(c_155201, plain, (![B_22518]: (B_22518='#skF_8' | ~r1_tarski(B_22518, '#skF_8'))), inference(resolution, [status(thm)], [c_155181, c_8])).
% 27.93/17.30  tff(c_155874, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_155852, c_155201])).
% 27.93/17.30  tff(c_155893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155496, c_155874])).
% 27.93/17.30  tff(c_155894, plain, (![B_22562]: (v1_funct_2('#skF_8', '#skF_8', B_22562))), inference(splitRight, [status(thm)], [c_155494])).
% 27.93/17.30  tff(c_155895, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_155494])).
% 27.93/17.30  tff(c_155923, plain, (~v1_funct_2('#skF_8', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_155895, c_167])).
% 27.93/17.30  tff(c_155954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155894, c_155923])).
% 27.93/17.30  tff(c_155955, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_155102])).
% 27.93/17.30  tff(c_155963, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_155955, c_78])).
% 27.93/17.30  tff(c_155969, plain, (![A_73]: (v1_funct_2('#skF_8', A_73, '#skF_8') | A_73='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_155016, c_155016, c_155016, c_155016, c_155016, c_88])).
% 27.93/17.30  tff(c_155970, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_155969])).
% 27.93/17.30  tff(c_155995, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_22, c_155970])).
% 27.93/17.30  tff(c_155999, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_155995])).
% 27.93/17.30  tff(c_156001, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(splitRight, [status(thm)], [c_155969])).
% 27.93/17.30  tff(c_156061, plain, (![A_22618, B_22619, C_22620]: (k1_relset_1(A_22618, B_22619, C_22620)=k1_relat_1(C_22620) | ~m1_subset_1(C_22620, k1_zfmisc_1(k2_zfmisc_1(A_22618, B_22619))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 27.93/17.30  tff(c_156167, plain, (![B_22642, C_22643]: (k1_relset_1('#skF_8', B_22642, C_22643)=k1_relat_1(C_22643) | ~m1_subset_1(C_22643, k1_zfmisc_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_155024, c_156061])).
% 27.93/17.30  tff(c_156169, plain, (![B_22642]: (k1_relset_1('#skF_8', B_22642, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_156001, c_156167])).
% 27.93/17.30  tff(c_156174, plain, (![B_22642]: (k1_relset_1('#skF_8', B_22642, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_155963, c_156169])).
% 27.93/17.30  tff(c_156192, plain, (![C_22645, B_22646]: (v1_funct_2(C_22645, '#skF_8', B_22646) | k1_relset_1('#skF_8', B_22646, C_22645)!='#skF_8' | ~m1_subset_1(C_22645, k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_155016, c_155016, c_155016, c_155016, c_85])).
% 27.93/17.30  tff(c_156194, plain, (![B_22646]: (v1_funct_2('#skF_8', '#skF_8', B_22646) | k1_relset_1('#skF_8', B_22646, '#skF_8')!='#skF_8')), inference(resolution, [status(thm)], [c_156001, c_156192])).
% 27.93/17.30  tff(c_156200, plain, (![B_22646]: (v1_funct_2('#skF_8', '#skF_8', B_22646))), inference(demodulation, [status(thm), theory('equality')], [c_156174, c_156194])).
% 27.93/17.30  tff(c_155960, plain, (~v1_funct_2('#skF_8', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_155955, c_167])).
% 27.93/17.30  tff(c_156204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156200, c_155960])).
% 27.93/17.30  tff(c_156205, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(splitRight, [status(thm)], [c_84])).
% 27.93/17.30  tff(c_162346, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_162326, c_156205])).
% 27.93/17.30  tff(c_162365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157569, c_162346])).
% 27.93/17.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.93/17.30  
% 27.93/17.30  Inference rules
% 27.93/17.30  ----------------------
% 27.93/17.30  #Ref     : 20
% 27.93/17.30  #Sup     : 33338
% 27.93/17.30  #Fact    : 0
% 27.93/17.30  #Define  : 0
% 27.93/17.30  #Split   : 455
% 27.93/17.30  #Chain   : 0
% 27.93/17.30  #Close   : 0
% 27.93/17.30  
% 27.93/17.30  Ordering : KBO
% 27.93/17.30  
% 27.93/17.30  Simplification rules
% 27.93/17.30  ----------------------
% 27.93/17.30  #Subsume      : 10238
% 27.93/17.30  #Demod        : 33335
% 27.93/17.30  #Tautology    : 9927
% 27.93/17.30  #SimpNegUnit  : 689
% 27.93/17.30  #BackRed      : 4187
% 27.93/17.30  
% 27.93/17.30  #Partial instantiations: 1923
% 27.93/17.30  #Strategies tried      : 1
% 27.93/17.30  
% 27.93/17.30  Timing (in seconds)
% 27.93/17.30  ----------------------
% 27.93/17.30  Preprocessing        : 0.35
% 27.93/17.30  Parsing              : 0.18
% 27.93/17.30  CNF conversion       : 0.03
% 27.93/17.30  Main loop            : 15.59
% 27.93/17.30  Inferencing          : 4.17
% 27.93/17.30  Reduction            : 5.73
% 27.93/17.30  Demodulation         : 4.15
% 27.93/17.30  BG Simplification    : 0.34
% 27.93/17.30  Subsumption          : 4.19
% 27.93/17.30  Abstraction          : 0.52
% 27.93/17.30  MUC search           : 0.00
% 27.93/17.30  Cooper               : 0.00
% 27.93/17.30  Total                : 16.54
% 27.93/17.30  Index Insertion      : 0.00
% 27.93/17.30  Index Deletion       : 0.00
% 27.93/17.30  Index Matching       : 0.00
% 27.93/17.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
