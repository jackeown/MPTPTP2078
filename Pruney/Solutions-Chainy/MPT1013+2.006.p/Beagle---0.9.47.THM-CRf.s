%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:35 EST 2020

% Result     : Theorem 11.04s
% Output     : CNFRefutation 11.19s
% Verified   : 
% Statistics : Number of formulae       :  155 (1553 expanded)
%              Number of leaves         :   34 ( 516 expanded)
%              Depth                    :   16
%              Number of atoms          :  259 (3466 expanded)
%              Number of equality atoms :  112 (1823 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
           => ( ( k2_relset_1(A,A,B) = A
                & k2_relset_1(A,A,C) = A )
             => k2_relset_1(A,A,k4_relset_1(A,A,A,A,C,B)) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_2)).

tff(f_112,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_84,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_491,plain,(
    ! [C_99,F_96,B_95,E_98,D_97,A_94] :
      ( k4_relset_1(A_94,B_95,C_99,D_97,E_98,F_96) = k5_relat_1(E_98,F_96)
      | ~ m1_subset_1(F_96,k1_zfmisc_1(k2_zfmisc_1(C_99,D_97)))
      | ~ m1_subset_1(E_98,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_660,plain,(
    ! [A_121,B_122,E_123] :
      ( k4_relset_1(A_121,B_122,'#skF_2','#skF_2',E_123,'#skF_3') = k5_relat_1(E_123,'#skF_3')
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(resolution,[status(thm)],[c_54,c_491])).

tff(c_677,plain,(
    k4_relset_1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_660])).

tff(c_40,plain,(
    ! [C_30,E_32,D_31,B_29,F_33,A_28] :
      ( m1_subset_1(k4_relset_1(A_28,B_29,C_30,D_31,E_32,F_33),k1_zfmisc_1(k2_zfmisc_1(A_28,D_31)))
      | ~ m1_subset_1(F_33,k1_zfmisc_1(k2_zfmisc_1(C_30,D_31)))
      | ~ m1_subset_1(E_32,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_812,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_40])).

tff(c_816,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_812])).

tff(c_42,plain,(
    ! [A_34,B_35,C_36] :
      ( k2_relset_1(A_34,B_35,C_36) = k2_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_839,plain,(
    k2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_4','#skF_3')) = k2_relat_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_816,c_42])).

tff(c_46,plain,(
    k2_relset_1('#skF_2','#skF_2',k4_relset_1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_4','#skF_3')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_808,plain,(
    k2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_4','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_46])).

tff(c_1401,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_808])).

tff(c_153,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_165,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_153])).

tff(c_50,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_347,plain,(
    ! [A_87,B_88,C_89] :
      ( k2_relset_1(A_87,B_88,C_89) = k2_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_353,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_347])).

tff(c_363,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_353])).

tff(c_48,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_350,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_347])).

tff(c_361,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_350])).

tff(c_164,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_153])).

tff(c_34,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_172,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_164,c_34])).

tff(c_182,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_392,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_182])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_267,plain,(
    ! [C_75,A_76,B_77] :
      ( r2_hidden(C_75,A_76)
      | ~ r2_hidden(C_75,B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_601,plain,(
    ! [A_110,B_111,A_112] :
      ( r2_hidden('#skF_1'(A_110,B_111),A_112)
      | ~ m1_subset_1(A_110,k1_zfmisc_1(A_112))
      | r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_6,c_267])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_647,plain,(
    ! [A_119,A_120] :
      ( ~ m1_subset_1(A_119,k1_zfmisc_1(A_120))
      | r1_tarski(A_119,A_120) ) ),
    inference(resolution,[status(thm)],[c_601,c_4])).

tff(c_659,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_647])).

tff(c_16,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( k1_relat_1(k2_zfmisc_1(A_16,B_17)) = A_16
      | k1_xboole_0 = B_17
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_271,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k1_relat_1(A_78),k1_relat_1(B_79))
      | ~ r1_tarski(A_78,B_79)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_277,plain,(
    ! [A_78,A_16,B_17] :
      ( r1_tarski(k1_relat_1(A_78),A_16)
      | ~ r1_tarski(A_78,k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(A_78)
      | k1_xboole_0 = B_17
      | k1_xboole_0 = A_16 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_271])).

tff(c_964,plain,(
    ! [A_127,A_128,B_129] :
      ( r1_tarski(k1_relat_1(A_127),A_128)
      | ~ r1_tarski(A_127,k2_zfmisc_1(A_128,B_129))
      | ~ v1_relat_1(A_127)
      | k1_xboole_0 = B_129
      | k1_xboole_0 = A_128 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_277])).

tff(c_974,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_3')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_659,c_964])).

tff(c_1008,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_974])).

tff(c_1009,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_392,c_1008])).

tff(c_28,plain,(
    ! [B_23,A_21] :
      ( k2_relat_1(k5_relat_1(B_23,A_21)) = k2_relat_1(A_21)
      | ~ r1_tarski(k1_relat_1(A_21),k2_relat_1(B_23))
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_396,plain,(
    ! [A_21] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_21)) = k2_relat_1(A_21)
      | ~ r1_tarski(k1_relat_1(A_21),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_28])).

tff(c_2376,plain,(
    ! [A_195] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_195)) = k2_relat_1(A_195)
      | ~ r1_tarski(k1_relat_1(A_195),'#skF_2')
      | ~ v1_relat_1(A_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_396])).

tff(c_2397,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1009,c_2376])).

tff(c_2428,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_363,c_2397])).

tff(c_2430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1401,c_2428])).

tff(c_2431,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_2432,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_2448,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_2432])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2437,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_2431,c_10])).

tff(c_2944,plain,(
    ! [A_256,B_257,C_258] :
      ( k2_relset_1(A_256,B_257,C_258) = k2_relat_1(C_258)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2953,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_2944])).

tff(c_2955,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2448,c_2953])).

tff(c_2957,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2955,c_2955,c_52])).

tff(c_2959,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_2957])).

tff(c_2986,plain,(
    ! [A_262,C_263] :
      ( k2_relset_1(A_262,'#skF_4',C_263) = k2_relat_1(C_263)
      | ~ m1_subset_1(C_263,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2437,c_2944])).

tff(c_2988,plain,(
    ! [A_262] : k2_relset_1(A_262,'#skF_4','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2959,c_2986])).

tff(c_2990,plain,(
    ! [A_262] : k2_relset_1(A_262,'#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2448,c_2988])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_99,plain,(
    ! [A_48,B_49] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_48,B_49)),A_48) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_102,plain,(
    ! [A_6] : r1_tarski(k1_relat_1(k1_xboole_0),A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_99])).

tff(c_106,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_102])).

tff(c_2436,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_106])).

tff(c_2441,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_2431,c_32])).

tff(c_3006,plain,(
    ! [B_265,A_266] :
      ( k2_relat_1(k5_relat_1(B_265,A_266)) = k2_relat_1(A_266)
      | ~ r1_tarski(k1_relat_1(A_266),k2_relat_1(B_265))
      | ~ v1_relat_1(B_265)
      | ~ v1_relat_1(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3018,plain,(
    ! [A_266] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_266)) = k2_relat_1(A_266)
      | ~ r1_tarski(k1_relat_1(A_266),'#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_266) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2448,c_3006])).

tff(c_3069,plain,(
    ! [A_271] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_271)) = k2_relat_1(A_271)
      | ~ r1_tarski(k1_relat_1(A_271),'#skF_4')
      | ~ v1_relat_1(A_271) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_3018])).

tff(c_3078,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_4')) = k2_relat_1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2441,c_3069])).

tff(c_3087,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_2436,c_2448,c_3078])).

tff(c_24,plain,(
    ! [A_18,B_20] :
      ( r1_tarski(k2_relat_1(A_18),k2_relat_1(B_20))
      | ~ r1_tarski(A_18,B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3106,plain,(
    ! [A_18] :
      ( r1_tarski(k2_relat_1(A_18),'#skF_4')
      | ~ r1_tarski(A_18,k5_relat_1('#skF_4','#skF_4'))
      | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_4'))
      | ~ v1_relat_1(A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3087,c_24])).

tff(c_3991,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_4','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3106])).

tff(c_12,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2439,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_4',B_7) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_2431,c_12])).

tff(c_3184,plain,(
    ! [B_278,C_282,E_281,A_277,D_280,F_279] :
      ( k4_relset_1(A_277,B_278,C_282,D_280,E_281,F_279) = k5_relat_1(E_281,F_279)
      | ~ m1_subset_1(F_279,k1_zfmisc_1(k2_zfmisc_1(C_282,D_280)))
      | ~ m1_subset_1(E_281,k1_zfmisc_1(k2_zfmisc_1(A_277,B_278))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_10361,plain,(
    ! [F_2452,E_2453,A_2456,B_2454,B_2455] :
      ( k4_relset_1(A_2456,B_2454,'#skF_4',B_2455,E_2453,F_2452) = k5_relat_1(E_2453,F_2452)
      | ~ m1_subset_1(F_2452,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(E_2453,k1_zfmisc_1(k2_zfmisc_1(A_2456,B_2454))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2439,c_3184])).

tff(c_10365,plain,(
    ! [A_2457,B_2458,B_2459,E_2460] :
      ( k4_relset_1(A_2457,B_2458,'#skF_4',B_2459,E_2460,'#skF_4') = k5_relat_1(E_2460,'#skF_4')
      | ~ m1_subset_1(E_2460,k1_zfmisc_1(k2_zfmisc_1(A_2457,B_2458))) ) ),
    inference(resolution,[status(thm)],[c_2959,c_10361])).

tff(c_10375,plain,(
    ! [A_2461,B_2462,E_2463] :
      ( k4_relset_1(A_2461,'#skF_4','#skF_4',B_2462,E_2463,'#skF_4') = k5_relat_1(E_2463,'#skF_4')
      | ~ m1_subset_1(E_2463,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2437,c_10365])).

tff(c_10378,plain,(
    ! [A_2461,B_2462] : k4_relset_1(A_2461,'#skF_4','#skF_4',B_2462,'#skF_4','#skF_4') = k5_relat_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2959,c_10375])).

tff(c_3435,plain,(
    ! [A_308,E_307,D_311,F_306,B_310,C_309] :
      ( m1_subset_1(k4_relset_1(A_308,B_310,C_309,D_311,E_307,F_306),k1_zfmisc_1(k2_zfmisc_1(A_308,D_311)))
      | ~ m1_subset_1(F_306,k1_zfmisc_1(k2_zfmisc_1(C_309,D_311)))
      | ~ m1_subset_1(E_307,k1_zfmisc_1(k2_zfmisc_1(A_308,B_310))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_38,plain,(
    ! [C_27,A_25,B_26] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3682,plain,(
    ! [A_341,C_339,D_340,B_344,F_342,E_343] :
      ( v1_relat_1(k4_relset_1(A_341,B_344,C_339,D_340,E_343,F_342))
      | ~ m1_subset_1(F_342,k1_zfmisc_1(k2_zfmisc_1(C_339,D_340)))
      | ~ m1_subset_1(E_343,k1_zfmisc_1(k2_zfmisc_1(A_341,B_344))) ) ),
    inference(resolution,[status(thm)],[c_3435,c_38])).

tff(c_6468,plain,(
    ! [A_498,B_500,B_499,F_501,E_497] :
      ( v1_relat_1(k4_relset_1(A_498,B_499,'#skF_4',B_500,E_497,F_501))
      | ~ m1_subset_1(F_501,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(E_497,k1_zfmisc_1(k2_zfmisc_1(A_498,B_499))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2439,c_3682])).

tff(c_6480,plain,(
    ! [A_511,B_512,B_513,E_514] :
      ( v1_relat_1(k4_relset_1(A_511,B_512,'#skF_4',B_513,E_514,'#skF_4'))
      | ~ m1_subset_1(E_514,k1_zfmisc_1(k2_zfmisc_1(A_511,B_512))) ) ),
    inference(resolution,[status(thm)],[c_2959,c_6468])).

tff(c_6488,plain,(
    ! [A_515,B_516,E_517] :
      ( v1_relat_1(k4_relset_1(A_515,'#skF_4','#skF_4',B_516,E_517,'#skF_4'))
      | ~ m1_subset_1(E_517,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2437,c_6480])).

tff(c_6491,plain,(
    ! [A_515,B_516] : v1_relat_1(k4_relset_1(A_515,'#skF_4','#skF_4',B_516,'#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2959,c_6488])).

tff(c_10381,plain,(
    v1_relat_1(k5_relat_1('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10378,c_6491])).

tff(c_10386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3991,c_10381])).

tff(c_10388,plain,(
    v1_relat_1(k5_relat_1('#skF_4','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3106])).

tff(c_2434,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) != '#skF_4'
      | A_24 = '#skF_4'
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_2431,c_34])).

tff(c_10470,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_4')) != '#skF_4'
    | k5_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10388,c_2434])).

tff(c_10474,plain,(
    k5_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3087,c_10470])).

tff(c_17770,plain,(
    ! [A_4606,B_4605,F_4603,E_4604,A_4607] :
      ( k4_relset_1(A_4607,B_4605,A_4606,'#skF_4',E_4604,F_4603) = k5_relat_1(E_4604,F_4603)
      | ~ m1_subset_1(F_4603,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(E_4604,k1_zfmisc_1(k2_zfmisc_1(A_4607,B_4605))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2437,c_3184])).

tff(c_17780,plain,(
    ! [A_4608,B_4609,A_4610,E_4611] :
      ( k4_relset_1(A_4608,B_4609,A_4610,'#skF_4',E_4611,'#skF_4') = k5_relat_1(E_4611,'#skF_4')
      | ~ m1_subset_1(E_4611,k1_zfmisc_1(k2_zfmisc_1(A_4608,B_4609))) ) ),
    inference(resolution,[status(thm)],[c_2959,c_17770])).

tff(c_17790,plain,(
    ! [A_4612,A_4613,E_4614] :
      ( k4_relset_1(A_4612,'#skF_4',A_4613,'#skF_4',E_4614,'#skF_4') = k5_relat_1(E_4614,'#skF_4')
      | ~ m1_subset_1(E_4614,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2437,c_17780])).

tff(c_17796,plain,(
    ! [A_4612,A_4613] : k4_relset_1(A_4612,'#skF_4',A_4613,'#skF_4','#skF_4','#skF_4') = k5_relat_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2959,c_17790])).

tff(c_17800,plain,(
    ! [A_4612,A_4613] : k4_relset_1(A_4612,'#skF_4',A_4613,'#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10474,c_17796])).

tff(c_180,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_165,c_34])).

tff(c_2528,plain,
    ( k2_relat_1('#skF_3') != '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_2431,c_180])).

tff(c_2529,plain,(
    k2_relat_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2528])).

tff(c_2713,plain,(
    ! [A_227,B_228,C_229] :
      ( k2_relset_1(A_227,B_228,C_229) = k2_relat_1(C_229)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2722,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_2713])).

tff(c_2727,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2448,c_48,c_2722])).

tff(c_2725,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2713])).

tff(c_2729,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2725])).

tff(c_2741,plain,(
    k2_relat_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2727,c_2729])).

tff(c_2742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2529,c_2741])).

tff(c_2743,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2528])).

tff(c_36,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_181,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_165,c_36])).

tff(c_2526,plain,
    ( k1_relat_1('#skF_3') != '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_2431,c_181])).

tff(c_2527,plain,(
    k1_relat_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2526])).

tff(c_2745,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2743,c_2527])).

tff(c_2752,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2441,c_2745])).

tff(c_2753,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2526])).

tff(c_2756,plain,(
    k2_relset_1('#skF_2','#skF_2',k4_relset_1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_4','#skF_4')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2753,c_46])).

tff(c_2956,plain,(
    k2_relset_1('#skF_4','#skF_4',k4_relset_1('#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2955,c_2955,c_2955,c_2955,c_2955,c_2955,c_2955,c_2756])).

tff(c_17804,plain,(
    k2_relset_1('#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17800,c_2956])).

tff(c_17808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2990,c_17804])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:44:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.04/4.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.04/4.31  
% 11.04/4.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.04/4.31  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 11.04/4.31  
% 11.04/4.31  %Foreground sorts:
% 11.04/4.31  
% 11.04/4.31  
% 11.04/4.31  %Background operators:
% 11.04/4.31  
% 11.04/4.31  
% 11.04/4.31  %Foreground operators:
% 11.04/4.31  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.04/4.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.04/4.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.04/4.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.04/4.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.04/4.31  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.04/4.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.04/4.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.04/4.31  tff('#skF_2', type, '#skF_2': $i).
% 11.04/4.31  tff('#skF_3', type, '#skF_3': $i).
% 11.04/4.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.04/4.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.04/4.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.04/4.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.04/4.31  tff('#skF_4', type, '#skF_4': $i).
% 11.04/4.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.04/4.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.04/4.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.04/4.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.04/4.31  
% 11.19/4.33  tff(f_124, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (((k2_relset_1(A, A, B) = A) & (k2_relset_1(A, A, C) = A)) => (k2_relset_1(A, A, k4_relset_1(A, A, A, A, C, B)) = A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_2)).
% 11.19/4.33  tff(f_112, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 11.19/4.33  tff(f_102, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 11.19/4.33  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.19/4.33  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.19/4.33  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 11.19/4.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.19/4.33  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 11.19/4.33  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.19/4.33  tff(f_61, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 11.19/4.33  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 11.19/4.33  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 11.19/4.33  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.19/4.33  tff(f_84, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 11.19/4.33  tff(f_49, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_relat_1)).
% 11.19/4.33  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.19/4.33  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.19/4.33  tff(c_491, plain, (![C_99, F_96, B_95, E_98, D_97, A_94]: (k4_relset_1(A_94, B_95, C_99, D_97, E_98, F_96)=k5_relat_1(E_98, F_96) | ~m1_subset_1(F_96, k1_zfmisc_1(k2_zfmisc_1(C_99, D_97))) | ~m1_subset_1(E_98, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.19/4.33  tff(c_660, plain, (![A_121, B_122, E_123]: (k4_relset_1(A_121, B_122, '#skF_2', '#skF_2', E_123, '#skF_3')=k5_relat_1(E_123, '#skF_3') | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(resolution, [status(thm)], [c_54, c_491])).
% 11.19/4.33  tff(c_677, plain, (k4_relset_1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_660])).
% 11.19/4.33  tff(c_40, plain, (![C_30, E_32, D_31, B_29, F_33, A_28]: (m1_subset_1(k4_relset_1(A_28, B_29, C_30, D_31, E_32, F_33), k1_zfmisc_1(k2_zfmisc_1(A_28, D_31))) | ~m1_subset_1(F_33, k1_zfmisc_1(k2_zfmisc_1(C_30, D_31))) | ~m1_subset_1(E_32, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.19/4.33  tff(c_812, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_677, c_40])).
% 11.19/4.33  tff(c_816, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_812])).
% 11.19/4.33  tff(c_42, plain, (![A_34, B_35, C_36]: (k2_relset_1(A_34, B_35, C_36)=k2_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.19/4.33  tff(c_839, plain, (k2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_4', '#skF_3'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_816, c_42])).
% 11.19/4.33  tff(c_46, plain, (k2_relset_1('#skF_2', '#skF_2', k4_relset_1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_4', '#skF_3'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.19/4.33  tff(c_808, plain, (k2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_4', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_677, c_46])).
% 11.19/4.33  tff(c_1401, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_839, c_808])).
% 11.19/4.33  tff(c_153, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.19/4.33  tff(c_165, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_153])).
% 11.19/4.33  tff(c_50, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.19/4.33  tff(c_347, plain, (![A_87, B_88, C_89]: (k2_relset_1(A_87, B_88, C_89)=k2_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.19/4.33  tff(c_353, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_347])).
% 11.19/4.33  tff(c_363, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_353])).
% 11.19/4.33  tff(c_48, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.19/4.33  tff(c_350, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_347])).
% 11.19/4.33  tff(c_361, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_350])).
% 11.19/4.33  tff(c_164, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_153])).
% 11.19/4.33  tff(c_34, plain, (![A_24]: (k2_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.19/4.33  tff(c_172, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_164, c_34])).
% 11.19/4.33  tff(c_182, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_172])).
% 11.19/4.33  tff(c_392, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_361, c_182])).
% 11.19/4.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.19/4.33  tff(c_267, plain, (![C_75, A_76, B_77]: (r2_hidden(C_75, A_76) | ~r2_hidden(C_75, B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.19/4.33  tff(c_601, plain, (![A_110, B_111, A_112]: (r2_hidden('#skF_1'(A_110, B_111), A_112) | ~m1_subset_1(A_110, k1_zfmisc_1(A_112)) | r1_tarski(A_110, B_111))), inference(resolution, [status(thm)], [c_6, c_267])).
% 11.19/4.33  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.19/4.33  tff(c_647, plain, (![A_119, A_120]: (~m1_subset_1(A_119, k1_zfmisc_1(A_120)) | r1_tarski(A_119, A_120))), inference(resolution, [status(thm)], [c_601, c_4])).
% 11.19/4.33  tff(c_659, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_647])).
% 11.19/4.33  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.19/4.33  tff(c_22, plain, (![A_16, B_17]: (k1_relat_1(k2_zfmisc_1(A_16, B_17))=A_16 | k1_xboole_0=B_17 | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.19/4.33  tff(c_271, plain, (![A_78, B_79]: (r1_tarski(k1_relat_1(A_78), k1_relat_1(B_79)) | ~r1_tarski(A_78, B_79) | ~v1_relat_1(B_79) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.19/4.33  tff(c_277, plain, (![A_78, A_16, B_17]: (r1_tarski(k1_relat_1(A_78), A_16) | ~r1_tarski(A_78, k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(A_78) | k1_xboole_0=B_17 | k1_xboole_0=A_16)), inference(superposition, [status(thm), theory('equality')], [c_22, c_271])).
% 11.19/4.33  tff(c_964, plain, (![A_127, A_128, B_129]: (r1_tarski(k1_relat_1(A_127), A_128) | ~r1_tarski(A_127, k2_zfmisc_1(A_128, B_129)) | ~v1_relat_1(A_127) | k1_xboole_0=B_129 | k1_xboole_0=A_128)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_277])).
% 11.19/4.33  tff(c_974, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1('#skF_3') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_659, c_964])).
% 11.19/4.33  tff(c_1008, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_974])).
% 11.19/4.33  tff(c_1009, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_392, c_1008])).
% 11.19/4.33  tff(c_28, plain, (![B_23, A_21]: (k2_relat_1(k5_relat_1(B_23, A_21))=k2_relat_1(A_21) | ~r1_tarski(k1_relat_1(A_21), k2_relat_1(B_23)) | ~v1_relat_1(B_23) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.19/4.33  tff(c_396, plain, (![A_21]: (k2_relat_1(k5_relat_1('#skF_4', A_21))=k2_relat_1(A_21) | ~r1_tarski(k1_relat_1(A_21), '#skF_2') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_21))), inference(superposition, [status(thm), theory('equality')], [c_361, c_28])).
% 11.19/4.33  tff(c_2376, plain, (![A_195]: (k2_relat_1(k5_relat_1('#skF_4', A_195))=k2_relat_1(A_195) | ~r1_tarski(k1_relat_1(A_195), '#skF_2') | ~v1_relat_1(A_195))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_396])).
% 11.19/4.33  tff(c_2397, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1009, c_2376])).
% 11.19/4.33  tff(c_2428, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_363, c_2397])).
% 11.19/4.33  tff(c_2430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1401, c_2428])).
% 11.19/4.33  tff(c_2431, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_172])).
% 11.19/4.33  tff(c_2432, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_172])).
% 11.19/4.33  tff(c_2448, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_2432])).
% 11.19/4.33  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.19/4.33  tff(c_2437, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_2431, c_10])).
% 11.19/4.33  tff(c_2944, plain, (![A_256, B_257, C_258]: (k2_relset_1(A_256, B_257, C_258)=k2_relat_1(C_258) | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.19/4.33  tff(c_2953, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_2944])).
% 11.19/4.33  tff(c_2955, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2448, c_2953])).
% 11.19/4.33  tff(c_2957, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2955, c_2955, c_52])).
% 11.19/4.33  tff(c_2959, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_2957])).
% 11.19/4.33  tff(c_2986, plain, (![A_262, C_263]: (k2_relset_1(A_262, '#skF_4', C_263)=k2_relat_1(C_263) | ~m1_subset_1(C_263, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2437, c_2944])).
% 11.19/4.33  tff(c_2988, plain, (![A_262]: (k2_relset_1(A_262, '#skF_4', '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2959, c_2986])).
% 11.19/4.33  tff(c_2990, plain, (![A_262]: (k2_relset_1(A_262, '#skF_4', '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2448, c_2988])).
% 11.19/4.33  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.19/4.33  tff(c_99, plain, (![A_48, B_49]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_48, B_49)), A_48))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.19/4.33  tff(c_102, plain, (![A_6]: (r1_tarski(k1_relat_1(k1_xboole_0), A_6))), inference(superposition, [status(thm), theory('equality')], [c_10, c_99])).
% 11.19/4.33  tff(c_106, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_102])).
% 11.19/4.33  tff(c_2436, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_106])).
% 11.19/4.33  tff(c_2441, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_2431, c_32])).
% 11.19/4.33  tff(c_3006, plain, (![B_265, A_266]: (k2_relat_1(k5_relat_1(B_265, A_266))=k2_relat_1(A_266) | ~r1_tarski(k1_relat_1(A_266), k2_relat_1(B_265)) | ~v1_relat_1(B_265) | ~v1_relat_1(A_266))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.19/4.33  tff(c_3018, plain, (![A_266]: (k2_relat_1(k5_relat_1('#skF_4', A_266))=k2_relat_1(A_266) | ~r1_tarski(k1_relat_1(A_266), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_266))), inference(superposition, [status(thm), theory('equality')], [c_2448, c_3006])).
% 11.19/4.33  tff(c_3069, plain, (![A_271]: (k2_relat_1(k5_relat_1('#skF_4', A_271))=k2_relat_1(A_271) | ~r1_tarski(k1_relat_1(A_271), '#skF_4') | ~v1_relat_1(A_271))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_3018])).
% 11.19/4.33  tff(c_3078, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_4'))=k2_relat_1('#skF_4') | ~r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2441, c_3069])).
% 11.19/4.33  tff(c_3087, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_2436, c_2448, c_3078])).
% 11.19/4.33  tff(c_24, plain, (![A_18, B_20]: (r1_tarski(k2_relat_1(A_18), k2_relat_1(B_20)) | ~r1_tarski(A_18, B_20) | ~v1_relat_1(B_20) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.19/4.33  tff(c_3106, plain, (![A_18]: (r1_tarski(k2_relat_1(A_18), '#skF_4') | ~r1_tarski(A_18, k5_relat_1('#skF_4', '#skF_4')) | ~v1_relat_1(k5_relat_1('#skF_4', '#skF_4')) | ~v1_relat_1(A_18))), inference(superposition, [status(thm), theory('equality')], [c_3087, c_24])).
% 11.19/4.33  tff(c_3991, plain, (~v1_relat_1(k5_relat_1('#skF_4', '#skF_4'))), inference(splitLeft, [status(thm)], [c_3106])).
% 11.19/4.33  tff(c_12, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.19/4.33  tff(c_2439, plain, (![B_7]: (k2_zfmisc_1('#skF_4', B_7)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_2431, c_12])).
% 11.19/4.33  tff(c_3184, plain, (![B_278, C_282, E_281, A_277, D_280, F_279]: (k4_relset_1(A_277, B_278, C_282, D_280, E_281, F_279)=k5_relat_1(E_281, F_279) | ~m1_subset_1(F_279, k1_zfmisc_1(k2_zfmisc_1(C_282, D_280))) | ~m1_subset_1(E_281, k1_zfmisc_1(k2_zfmisc_1(A_277, B_278))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.19/4.33  tff(c_10361, plain, (![F_2452, E_2453, A_2456, B_2454, B_2455]: (k4_relset_1(A_2456, B_2454, '#skF_4', B_2455, E_2453, F_2452)=k5_relat_1(E_2453, F_2452) | ~m1_subset_1(F_2452, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(E_2453, k1_zfmisc_1(k2_zfmisc_1(A_2456, B_2454))))), inference(superposition, [status(thm), theory('equality')], [c_2439, c_3184])).
% 11.19/4.33  tff(c_10365, plain, (![A_2457, B_2458, B_2459, E_2460]: (k4_relset_1(A_2457, B_2458, '#skF_4', B_2459, E_2460, '#skF_4')=k5_relat_1(E_2460, '#skF_4') | ~m1_subset_1(E_2460, k1_zfmisc_1(k2_zfmisc_1(A_2457, B_2458))))), inference(resolution, [status(thm)], [c_2959, c_10361])).
% 11.19/4.33  tff(c_10375, plain, (![A_2461, B_2462, E_2463]: (k4_relset_1(A_2461, '#skF_4', '#skF_4', B_2462, E_2463, '#skF_4')=k5_relat_1(E_2463, '#skF_4') | ~m1_subset_1(E_2463, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2437, c_10365])).
% 11.19/4.33  tff(c_10378, plain, (![A_2461, B_2462]: (k4_relset_1(A_2461, '#skF_4', '#skF_4', B_2462, '#skF_4', '#skF_4')=k5_relat_1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_2959, c_10375])).
% 11.19/4.33  tff(c_3435, plain, (![A_308, E_307, D_311, F_306, B_310, C_309]: (m1_subset_1(k4_relset_1(A_308, B_310, C_309, D_311, E_307, F_306), k1_zfmisc_1(k2_zfmisc_1(A_308, D_311))) | ~m1_subset_1(F_306, k1_zfmisc_1(k2_zfmisc_1(C_309, D_311))) | ~m1_subset_1(E_307, k1_zfmisc_1(k2_zfmisc_1(A_308, B_310))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.19/4.33  tff(c_38, plain, (![C_27, A_25, B_26]: (v1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.19/4.33  tff(c_3682, plain, (![A_341, C_339, D_340, B_344, F_342, E_343]: (v1_relat_1(k4_relset_1(A_341, B_344, C_339, D_340, E_343, F_342)) | ~m1_subset_1(F_342, k1_zfmisc_1(k2_zfmisc_1(C_339, D_340))) | ~m1_subset_1(E_343, k1_zfmisc_1(k2_zfmisc_1(A_341, B_344))))), inference(resolution, [status(thm)], [c_3435, c_38])).
% 11.19/4.33  tff(c_6468, plain, (![A_498, B_500, B_499, F_501, E_497]: (v1_relat_1(k4_relset_1(A_498, B_499, '#skF_4', B_500, E_497, F_501)) | ~m1_subset_1(F_501, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(E_497, k1_zfmisc_1(k2_zfmisc_1(A_498, B_499))))), inference(superposition, [status(thm), theory('equality')], [c_2439, c_3682])).
% 11.19/4.33  tff(c_6480, plain, (![A_511, B_512, B_513, E_514]: (v1_relat_1(k4_relset_1(A_511, B_512, '#skF_4', B_513, E_514, '#skF_4')) | ~m1_subset_1(E_514, k1_zfmisc_1(k2_zfmisc_1(A_511, B_512))))), inference(resolution, [status(thm)], [c_2959, c_6468])).
% 11.19/4.33  tff(c_6488, plain, (![A_515, B_516, E_517]: (v1_relat_1(k4_relset_1(A_515, '#skF_4', '#skF_4', B_516, E_517, '#skF_4')) | ~m1_subset_1(E_517, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2437, c_6480])).
% 11.19/4.33  tff(c_6491, plain, (![A_515, B_516]: (v1_relat_1(k4_relset_1(A_515, '#skF_4', '#skF_4', B_516, '#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_2959, c_6488])).
% 11.19/4.33  tff(c_10381, plain, (v1_relat_1(k5_relat_1('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10378, c_6491])).
% 11.19/4.33  tff(c_10386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3991, c_10381])).
% 11.19/4.33  tff(c_10388, plain, (v1_relat_1(k5_relat_1('#skF_4', '#skF_4'))), inference(splitRight, [status(thm)], [c_3106])).
% 11.19/4.33  tff(c_2434, plain, (![A_24]: (k2_relat_1(A_24)!='#skF_4' | A_24='#skF_4' | ~v1_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_2431, c_34])).
% 11.19/4.33  tff(c_10470, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_4'))!='#skF_4' | k5_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_10388, c_2434])).
% 11.19/4.33  tff(c_10474, plain, (k5_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3087, c_10470])).
% 11.19/4.33  tff(c_17770, plain, (![A_4606, B_4605, F_4603, E_4604, A_4607]: (k4_relset_1(A_4607, B_4605, A_4606, '#skF_4', E_4604, F_4603)=k5_relat_1(E_4604, F_4603) | ~m1_subset_1(F_4603, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(E_4604, k1_zfmisc_1(k2_zfmisc_1(A_4607, B_4605))))), inference(superposition, [status(thm), theory('equality')], [c_2437, c_3184])).
% 11.19/4.33  tff(c_17780, plain, (![A_4608, B_4609, A_4610, E_4611]: (k4_relset_1(A_4608, B_4609, A_4610, '#skF_4', E_4611, '#skF_4')=k5_relat_1(E_4611, '#skF_4') | ~m1_subset_1(E_4611, k1_zfmisc_1(k2_zfmisc_1(A_4608, B_4609))))), inference(resolution, [status(thm)], [c_2959, c_17770])).
% 11.19/4.33  tff(c_17790, plain, (![A_4612, A_4613, E_4614]: (k4_relset_1(A_4612, '#skF_4', A_4613, '#skF_4', E_4614, '#skF_4')=k5_relat_1(E_4614, '#skF_4') | ~m1_subset_1(E_4614, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2437, c_17780])).
% 11.19/4.33  tff(c_17796, plain, (![A_4612, A_4613]: (k4_relset_1(A_4612, '#skF_4', A_4613, '#skF_4', '#skF_4', '#skF_4')=k5_relat_1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_2959, c_17790])).
% 11.19/4.33  tff(c_17800, plain, (![A_4612, A_4613]: (k4_relset_1(A_4612, '#skF_4', A_4613, '#skF_4', '#skF_4', '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10474, c_17796])).
% 11.19/4.33  tff(c_180, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_165, c_34])).
% 11.19/4.33  tff(c_2528, plain, (k2_relat_1('#skF_3')!='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_2431, c_180])).
% 11.19/4.33  tff(c_2529, plain, (k2_relat_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_2528])).
% 11.19/4.33  tff(c_2713, plain, (![A_227, B_228, C_229]: (k2_relset_1(A_227, B_228, C_229)=k2_relat_1(C_229) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_227, B_228))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.19/4.33  tff(c_2722, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_2713])).
% 11.19/4.33  tff(c_2727, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2448, c_48, c_2722])).
% 11.19/4.33  tff(c_2725, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_2713])).
% 11.19/4.33  tff(c_2729, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2725])).
% 11.19/4.33  tff(c_2741, plain, (k2_relat_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2727, c_2729])).
% 11.19/4.33  tff(c_2742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2529, c_2741])).
% 11.19/4.33  tff(c_2743, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_2528])).
% 11.19/4.33  tff(c_36, plain, (![A_24]: (k1_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.19/4.33  tff(c_181, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_165, c_36])).
% 11.19/4.33  tff(c_2526, plain, (k1_relat_1('#skF_3')!='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_2431, c_181])).
% 11.19/4.33  tff(c_2527, plain, (k1_relat_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_2526])).
% 11.19/4.33  tff(c_2745, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2743, c_2527])).
% 11.19/4.33  tff(c_2752, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2441, c_2745])).
% 11.19/4.33  tff(c_2753, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_2526])).
% 11.19/4.33  tff(c_2756, plain, (k2_relset_1('#skF_2', '#skF_2', k4_relset_1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_4', '#skF_4'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2753, c_46])).
% 11.19/4.33  tff(c_2956, plain, (k2_relset_1('#skF_4', '#skF_4', k4_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2955, c_2955, c_2955, c_2955, c_2955, c_2955, c_2955, c_2756])).
% 11.19/4.33  tff(c_17804, plain, (k2_relset_1('#skF_4', '#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17800, c_2956])).
% 11.19/4.33  tff(c_17808, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2990, c_17804])).
% 11.19/4.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.19/4.33  
% 11.19/4.33  Inference rules
% 11.19/4.33  ----------------------
% 11.19/4.33  #Ref     : 0
% 11.19/4.33  #Sup     : 4617
% 11.19/4.33  #Fact    : 4
% 11.19/4.33  #Define  : 0
% 11.19/4.33  #Split   : 38
% 11.19/4.33  #Chain   : 0
% 11.19/4.33  #Close   : 0
% 11.19/4.33  
% 11.19/4.33  Ordering : KBO
% 11.19/4.33  
% 11.19/4.33  Simplification rules
% 11.19/4.33  ----------------------
% 11.19/4.33  #Subsume      : 1051
% 11.19/4.33  #Demod        : 2745
% 11.19/4.33  #Tautology    : 945
% 11.19/4.33  #SimpNegUnit  : 18
% 11.19/4.33  #BackRed      : 44
% 11.19/4.33  
% 11.19/4.33  #Partial instantiations: 0
% 11.19/4.33  #Strategies tried      : 1
% 11.19/4.33  
% 11.19/4.33  Timing (in seconds)
% 11.19/4.33  ----------------------
% 11.19/4.33  Preprocessing        : 0.32
% 11.19/4.33  Parsing              : 0.17
% 11.19/4.33  CNF conversion       : 0.02
% 11.19/4.33  Main loop            : 3.16
% 11.19/4.33  Inferencing          : 0.81
% 11.19/4.33  Reduction            : 0.84
% 11.19/4.34  Demodulation         : 0.60
% 11.19/4.34  BG Simplification    : 0.12
% 11.19/4.34  Subsumption          : 1.18
% 11.19/4.34  Abstraction          : 0.16
% 11.19/4.34  MUC search           : 0.00
% 11.19/4.34  Cooper               : 0.00
% 11.19/4.34  Total                : 3.53
% 11.19/4.34  Index Insertion      : 0.00
% 11.19/4.34  Index Deletion       : 0.00
% 11.19/4.34  Index Matching       : 0.00
% 11.19/4.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
