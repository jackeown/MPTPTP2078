%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:26 EST 2020

% Result     : Theorem 7.35s
% Output     : CNFRefutation 7.35s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 233 expanded)
%              Number of leaves         :   44 ( 100 expanded)
%              Depth                    :   13
%              Number of atoms          :  180 ( 601 expanded)
%              Number of equality atoms :   50 ( 175 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
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

tff(f_93,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_76,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2955,plain,(
    ! [A_473,B_474,C_475] :
      ( k2_relset_1(A_473,B_474,C_475) = k2_relat_1(C_475)
      | ~ m1_subset_1(C_475,k1_zfmisc_1(k2_zfmisc_1(A_473,B_474))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2964,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_2955])).

tff(c_74,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2965,plain,(
    k2_relat_1('#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2964,c_74])).

tff(c_24,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_113,plain,(
    ! [B_94,A_95] :
      ( v1_relat_1(B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_95))
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_119,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_76,c_113])).

tff(c_123,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_119])).

tff(c_179,plain,(
    ! [C_109,B_110,A_111] :
      ( v5_relat_1(C_109,B_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_188,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_76,c_179])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k2_relat_1(B_15),A_14)
      | ~ v5_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2939,plain,(
    ! [A_471,B_472] :
      ( r2_hidden('#skF_1'(A_471,B_472),B_472)
      | r2_hidden('#skF_2'(A_471,B_472),A_471)
      | B_472 = A_471 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5590,plain,(
    ! [A_788,B_789,A_790] :
      ( r2_hidden('#skF_2'(A_788,B_789),A_790)
      | ~ m1_subset_1(A_788,k1_zfmisc_1(A_790))
      | r2_hidden('#skF_1'(A_788,B_789),B_789)
      | B_789 = A_788 ) ),
    inference(resolution,[status(thm)],[c_2939,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5643,plain,(
    ! [A_791,A_792] :
      ( ~ m1_subset_1(A_791,k1_zfmisc_1(A_792))
      | r2_hidden('#skF_1'(A_791,A_792),A_792)
      | A_792 = A_791 ) ),
    inference(resolution,[status(thm)],[c_5590,c_4])).

tff(c_84,plain,(
    ! [D_80] :
      ( r2_hidden('#skF_10'(D_80),'#skF_7')
      | ~ r2_hidden(D_80,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_78,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2896,plain,(
    ! [A_461,B_462,C_463] :
      ( k1_relset_1(A_461,B_462,C_463) = k1_relat_1(C_463)
      | ~ m1_subset_1(C_463,k1_zfmisc_1(k2_zfmisc_1(A_461,B_462))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2905,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_2896])).

tff(c_3846,plain,(
    ! [B_588,A_589,C_590] :
      ( k1_xboole_0 = B_588
      | k1_relset_1(A_589,B_588,C_590) = A_589
      | ~ v1_funct_2(C_590,A_589,B_588)
      | ~ m1_subset_1(C_590,k1_zfmisc_1(k2_zfmisc_1(A_589,B_588))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3853,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_76,c_3846])).

tff(c_3857,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2905,c_3853])).

tff(c_3858,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_3857])).

tff(c_80,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_82,plain,(
    ! [D_80] :
      ( k1_funct_1('#skF_9','#skF_10'(D_80)) = D_80
      | ~ r2_hidden(D_80,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_3037,plain,(
    ! [A_492,D_493] :
      ( r2_hidden(k1_funct_1(A_492,D_493),k2_relat_1(A_492))
      | ~ r2_hidden(D_493,k1_relat_1(A_492))
      | ~ v1_funct_1(A_492)
      | ~ v1_relat_1(A_492) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3045,plain,(
    ! [D_80] :
      ( r2_hidden(D_80,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_10'(D_80),k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_80,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_3037])).

tff(c_3049,plain,(
    ! [D_80] :
      ( r2_hidden(D_80,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_10'(D_80),k1_relat_1('#skF_9'))
      | ~ r2_hidden(D_80,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_80,c_3045])).

tff(c_3954,plain,(
    ! [D_598] :
      ( r2_hidden(D_598,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_10'(D_598),'#skF_7')
      | ~ r2_hidden(D_598,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3858,c_3049])).

tff(c_3967,plain,(
    ! [D_80] :
      ( r2_hidden(D_80,k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_80,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_84,c_3954])).

tff(c_2832,plain,(
    ! [A_450,B_451] :
      ( ~ r2_hidden('#skF_1'(A_450,B_451),A_450)
      | r2_hidden('#skF_2'(A_450,B_451),A_450)
      | B_451 = A_450 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5389,plain,(
    ! [A_751,B_752,A_753] :
      ( r2_hidden('#skF_2'(A_751,B_752),A_753)
      | ~ m1_subset_1(A_751,k1_zfmisc_1(A_753))
      | ~ r2_hidden('#skF_1'(A_751,B_752),A_751)
      | B_752 = A_751 ) ),
    inference(resolution,[status(thm)],[c_2832,c_12])).

tff(c_5449,plain,(
    ! [B_760,A_761] :
      ( r2_hidden('#skF_2'(k2_relat_1('#skF_9'),B_760),A_761)
      | ~ m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1(A_761))
      | k2_relat_1('#skF_9') = B_760
      | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_9'),B_760),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3967,c_5389])).

tff(c_3968,plain,(
    ! [D_599] :
      ( r2_hidden(D_599,k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_599,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_84,c_3954])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3994,plain,(
    ! [B_2] :
      ( ~ r2_hidden('#skF_2'(k2_relat_1('#skF_9'),B_2),B_2)
      | k2_relat_1('#skF_9') = B_2
      | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_9'),B_2),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3968,c_2])).

tff(c_5466,plain,(
    ! [A_761] :
      ( ~ m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1(A_761))
      | k2_relat_1('#skF_9') = A_761
      | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_9'),A_761),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_5449,c_3994])).

tff(c_5647,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | k2_relat_1('#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_5643,c_5466])).

tff(c_5668,plain,(
    ~ m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_2965,c_2965,c_5647])).

tff(c_5681,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_16,c_5668])).

tff(c_5684,plain,
    ( ~ v5_relat_1('#skF_9','#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_22,c_5681])).

tff(c_5688,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_188,c_5684])).

tff(c_5689,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3857])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_52,plain,(
    ! [B_64,A_63] :
      ( ~ r1_tarski(B_64,A_63)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3050,plain,(
    ! [B_494,A_495] :
      ( ~ r1_tarski(B_494,'#skF_1'(A_495,B_494))
      | r2_hidden('#skF_2'(A_495,B_494),A_495)
      | B_494 = A_495 ) ),
    inference(resolution,[status(thm)],[c_2939,c_52])).

tff(c_3059,plain,(
    ! [A_496] :
      ( r2_hidden('#skF_2'(A_496,k1_xboole_0),A_496)
      | k1_xboole_0 = A_496 ) ),
    inference(resolution,[status(thm)],[c_10,c_3050])).

tff(c_3097,plain,(
    ! [A_499,A_500] :
      ( r2_hidden('#skF_2'(A_499,k1_xboole_0),A_500)
      | ~ m1_subset_1(A_499,k1_zfmisc_1(A_500))
      | k1_xboole_0 = A_499 ) ),
    inference(resolution,[status(thm)],[c_3059,c_12])).

tff(c_3198,plain,(
    ! [A_506] :
      ( r2_hidden('#skF_1'(A_506,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(A_506,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = A_506 ) ),
    inference(resolution,[status(thm)],[c_3097,c_4])).

tff(c_3210,plain,(
    ! [A_506] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_1'(A_506,k1_xboole_0))
      | ~ m1_subset_1(A_506,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = A_506 ) ),
    inference(resolution,[status(thm)],[c_3198,c_52])).

tff(c_3226,plain,(
    ! [A_507] :
      ( ~ m1_subset_1(A_507,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = A_507 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3210])).

tff(c_3231,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_3226])).

tff(c_5931,plain,(
    ! [A_808] :
      ( A_808 = '#skF_8'
      | ~ r1_tarski(A_808,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5689,c_5689,c_3231])).

tff(c_6095,plain,(
    ! [B_825] :
      ( k2_relat_1(B_825) = '#skF_8'
      | ~ v5_relat_1(B_825,'#skF_8')
      | ~ v1_relat_1(B_825) ) ),
    inference(resolution,[status(thm)],[c_22,c_5931])).

tff(c_6102,plain,
    ( k2_relat_1('#skF_9') = '#skF_8'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_188,c_6095])).

tff(c_6108,plain,(
    k2_relat_1('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_6102])).

tff(c_6110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2965,c_6108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:39:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.35/2.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.35/2.57  
% 7.35/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.35/2.57  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 7.35/2.57  
% 7.35/2.57  %Foreground sorts:
% 7.35/2.57  
% 7.35/2.57  
% 7.35/2.57  %Background operators:
% 7.35/2.57  
% 7.35/2.57  
% 7.35/2.57  %Foreground operators:
% 7.35/2.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.35/2.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.35/2.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.35/2.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.35/2.57  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.35/2.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.35/2.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.35/2.57  tff('#skF_7', type, '#skF_7': $i).
% 7.35/2.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.35/2.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.35/2.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.35/2.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.35/2.57  tff('#skF_10', type, '#skF_10': $i > $i).
% 7.35/2.57  tff('#skF_9', type, '#skF_9': $i).
% 7.35/2.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.35/2.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.35/2.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.35/2.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.35/2.57  tff('#skF_8', type, '#skF_8': $i).
% 7.35/2.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.35/2.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.35/2.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.35/2.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.35/2.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.35/2.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.35/2.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.35/2.57  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.35/2.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.35/2.57  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.35/2.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.35/2.57  
% 7.35/2.59  tff(f_149, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 7.35/2.59  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.35/2.59  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.35/2.59  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.35/2.59  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.35/2.59  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 7.35/2.59  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.35/2.59  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 7.35/2.59  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 7.35/2.59  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.35/2.59  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.35/2.59  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 7.35/2.59  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.35/2.59  tff(f_98, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.35/2.59  tff(c_76, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.35/2.59  tff(c_2955, plain, (![A_473, B_474, C_475]: (k2_relset_1(A_473, B_474, C_475)=k2_relat_1(C_475) | ~m1_subset_1(C_475, k1_zfmisc_1(k2_zfmisc_1(A_473, B_474))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.35/2.59  tff(c_2964, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_76, c_2955])).
% 7.35/2.59  tff(c_74, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.35/2.59  tff(c_2965, plain, (k2_relat_1('#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2964, c_74])).
% 7.35/2.59  tff(c_24, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.35/2.59  tff(c_113, plain, (![B_94, A_95]: (v1_relat_1(B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(A_95)) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.35/2.59  tff(c_119, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_76, c_113])).
% 7.35/2.59  tff(c_123, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_119])).
% 7.35/2.59  tff(c_179, plain, (![C_109, B_110, A_111]: (v5_relat_1(C_109, B_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.35/2.59  tff(c_188, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_76, c_179])).
% 7.35/2.59  tff(c_22, plain, (![B_15, A_14]: (r1_tarski(k2_relat_1(B_15), A_14) | ~v5_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.35/2.59  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.35/2.59  tff(c_2939, plain, (![A_471, B_472]: (r2_hidden('#skF_1'(A_471, B_472), B_472) | r2_hidden('#skF_2'(A_471, B_472), A_471) | B_472=A_471)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.35/2.59  tff(c_12, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.35/2.59  tff(c_5590, plain, (![A_788, B_789, A_790]: (r2_hidden('#skF_2'(A_788, B_789), A_790) | ~m1_subset_1(A_788, k1_zfmisc_1(A_790)) | r2_hidden('#skF_1'(A_788, B_789), B_789) | B_789=A_788)), inference(resolution, [status(thm)], [c_2939, c_12])).
% 7.35/2.59  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.35/2.59  tff(c_5643, plain, (![A_791, A_792]: (~m1_subset_1(A_791, k1_zfmisc_1(A_792)) | r2_hidden('#skF_1'(A_791, A_792), A_792) | A_792=A_791)), inference(resolution, [status(thm)], [c_5590, c_4])).
% 7.35/2.59  tff(c_84, plain, (![D_80]: (r2_hidden('#skF_10'(D_80), '#skF_7') | ~r2_hidden(D_80, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.35/2.59  tff(c_78, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.35/2.59  tff(c_2896, plain, (![A_461, B_462, C_463]: (k1_relset_1(A_461, B_462, C_463)=k1_relat_1(C_463) | ~m1_subset_1(C_463, k1_zfmisc_1(k2_zfmisc_1(A_461, B_462))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.35/2.59  tff(c_2905, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_76, c_2896])).
% 7.35/2.59  tff(c_3846, plain, (![B_588, A_589, C_590]: (k1_xboole_0=B_588 | k1_relset_1(A_589, B_588, C_590)=A_589 | ~v1_funct_2(C_590, A_589, B_588) | ~m1_subset_1(C_590, k1_zfmisc_1(k2_zfmisc_1(A_589, B_588))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.35/2.59  tff(c_3853, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_76, c_3846])).
% 7.35/2.59  tff(c_3857, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2905, c_3853])).
% 7.35/2.59  tff(c_3858, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_3857])).
% 7.35/2.59  tff(c_80, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.35/2.59  tff(c_82, plain, (![D_80]: (k1_funct_1('#skF_9', '#skF_10'(D_80))=D_80 | ~r2_hidden(D_80, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.35/2.59  tff(c_3037, plain, (![A_492, D_493]: (r2_hidden(k1_funct_1(A_492, D_493), k2_relat_1(A_492)) | ~r2_hidden(D_493, k1_relat_1(A_492)) | ~v1_funct_1(A_492) | ~v1_relat_1(A_492))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.35/2.59  tff(c_3045, plain, (![D_80]: (r2_hidden(D_80, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_10'(D_80), k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_80, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_3037])).
% 7.35/2.59  tff(c_3049, plain, (![D_80]: (r2_hidden(D_80, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_10'(D_80), k1_relat_1('#skF_9')) | ~r2_hidden(D_80, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_80, c_3045])).
% 7.35/2.59  tff(c_3954, plain, (![D_598]: (r2_hidden(D_598, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_10'(D_598), '#skF_7') | ~r2_hidden(D_598, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3858, c_3049])).
% 7.35/2.59  tff(c_3967, plain, (![D_80]: (r2_hidden(D_80, k2_relat_1('#skF_9')) | ~r2_hidden(D_80, '#skF_8'))), inference(resolution, [status(thm)], [c_84, c_3954])).
% 7.35/2.59  tff(c_2832, plain, (![A_450, B_451]: (~r2_hidden('#skF_1'(A_450, B_451), A_450) | r2_hidden('#skF_2'(A_450, B_451), A_450) | B_451=A_450)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.35/2.59  tff(c_5389, plain, (![A_751, B_752, A_753]: (r2_hidden('#skF_2'(A_751, B_752), A_753) | ~m1_subset_1(A_751, k1_zfmisc_1(A_753)) | ~r2_hidden('#skF_1'(A_751, B_752), A_751) | B_752=A_751)), inference(resolution, [status(thm)], [c_2832, c_12])).
% 7.35/2.59  tff(c_5449, plain, (![B_760, A_761]: (r2_hidden('#skF_2'(k2_relat_1('#skF_9'), B_760), A_761) | ~m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1(A_761)) | k2_relat_1('#skF_9')=B_760 | ~r2_hidden('#skF_1'(k2_relat_1('#skF_9'), B_760), '#skF_8'))), inference(resolution, [status(thm)], [c_3967, c_5389])).
% 7.35/2.59  tff(c_3968, plain, (![D_599]: (r2_hidden(D_599, k2_relat_1('#skF_9')) | ~r2_hidden(D_599, '#skF_8'))), inference(resolution, [status(thm)], [c_84, c_3954])).
% 7.35/2.59  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.35/2.59  tff(c_3994, plain, (![B_2]: (~r2_hidden('#skF_2'(k2_relat_1('#skF_9'), B_2), B_2) | k2_relat_1('#skF_9')=B_2 | ~r2_hidden('#skF_1'(k2_relat_1('#skF_9'), B_2), '#skF_8'))), inference(resolution, [status(thm)], [c_3968, c_2])).
% 7.35/2.59  tff(c_5466, plain, (![A_761]: (~m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1(A_761)) | k2_relat_1('#skF_9')=A_761 | ~r2_hidden('#skF_1'(k2_relat_1('#skF_9'), A_761), '#skF_8'))), inference(resolution, [status(thm)], [c_5449, c_3994])).
% 7.35/2.59  tff(c_5647, plain, (~m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | k2_relat_1('#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_5643, c_5466])).
% 7.35/2.59  tff(c_5668, plain, (~m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_2965, c_2965, c_5647])).
% 7.35/2.59  tff(c_5681, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_16, c_5668])).
% 7.35/2.59  tff(c_5684, plain, (~v5_relat_1('#skF_9', '#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_22, c_5681])).
% 7.35/2.59  tff(c_5688, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_188, c_5684])).
% 7.35/2.59  tff(c_5689, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_3857])).
% 7.35/2.59  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.35/2.59  tff(c_52, plain, (![B_64, A_63]: (~r1_tarski(B_64, A_63) | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.35/2.59  tff(c_3050, plain, (![B_494, A_495]: (~r1_tarski(B_494, '#skF_1'(A_495, B_494)) | r2_hidden('#skF_2'(A_495, B_494), A_495) | B_494=A_495)), inference(resolution, [status(thm)], [c_2939, c_52])).
% 7.35/2.59  tff(c_3059, plain, (![A_496]: (r2_hidden('#skF_2'(A_496, k1_xboole_0), A_496) | k1_xboole_0=A_496)), inference(resolution, [status(thm)], [c_10, c_3050])).
% 7.35/2.59  tff(c_3097, plain, (![A_499, A_500]: (r2_hidden('#skF_2'(A_499, k1_xboole_0), A_500) | ~m1_subset_1(A_499, k1_zfmisc_1(A_500)) | k1_xboole_0=A_499)), inference(resolution, [status(thm)], [c_3059, c_12])).
% 7.35/2.59  tff(c_3198, plain, (![A_506]: (r2_hidden('#skF_1'(A_506, k1_xboole_0), k1_xboole_0) | ~m1_subset_1(A_506, k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0=A_506)), inference(resolution, [status(thm)], [c_3097, c_4])).
% 7.35/2.59  tff(c_3210, plain, (![A_506]: (~r1_tarski(k1_xboole_0, '#skF_1'(A_506, k1_xboole_0)) | ~m1_subset_1(A_506, k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0=A_506)), inference(resolution, [status(thm)], [c_3198, c_52])).
% 7.35/2.59  tff(c_3226, plain, (![A_507]: (~m1_subset_1(A_507, k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0=A_507)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3210])).
% 7.35/2.59  tff(c_3231, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_3226])).
% 7.35/2.59  tff(c_5931, plain, (![A_808]: (A_808='#skF_8' | ~r1_tarski(A_808, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_5689, c_5689, c_3231])).
% 7.35/2.59  tff(c_6095, plain, (![B_825]: (k2_relat_1(B_825)='#skF_8' | ~v5_relat_1(B_825, '#skF_8') | ~v1_relat_1(B_825))), inference(resolution, [status(thm)], [c_22, c_5931])).
% 7.35/2.59  tff(c_6102, plain, (k2_relat_1('#skF_9')='#skF_8' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_188, c_6095])).
% 7.35/2.59  tff(c_6108, plain, (k2_relat_1('#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_6102])).
% 7.35/2.59  tff(c_6110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2965, c_6108])).
% 7.35/2.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.35/2.59  
% 7.35/2.59  Inference rules
% 7.35/2.59  ----------------------
% 7.35/2.59  #Ref     : 2
% 7.35/2.59  #Sup     : 1123
% 7.35/2.59  #Fact    : 0
% 7.35/2.59  #Define  : 0
% 7.35/2.59  #Split   : 43
% 7.35/2.59  #Chain   : 0
% 7.35/2.59  #Close   : 0
% 7.35/2.59  
% 7.35/2.59  Ordering : KBO
% 7.35/2.59  
% 7.35/2.59  Simplification rules
% 7.35/2.59  ----------------------
% 7.35/2.59  #Subsume      : 311
% 7.35/2.59  #Demod        : 1269
% 7.35/2.59  #Tautology    : 223
% 7.35/2.59  #SimpNegUnit  : 79
% 7.35/2.59  #BackRed      : 437
% 7.35/2.59  
% 7.35/2.59  #Partial instantiations: 0
% 7.35/2.59  #Strategies tried      : 1
% 7.35/2.59  
% 7.35/2.59  Timing (in seconds)
% 7.35/2.59  ----------------------
% 7.35/2.59  Preprocessing        : 0.36
% 7.35/2.59  Parsing              : 0.18
% 7.35/2.59  CNF conversion       : 0.03
% 7.35/2.59  Main loop            : 1.47
% 7.35/2.59  Inferencing          : 0.49
% 7.35/2.59  Reduction            : 0.45
% 7.35/2.59  Demodulation         : 0.28
% 7.35/2.59  BG Simplification    : 0.05
% 7.35/2.59  Subsumption          : 0.34
% 7.35/2.59  Abstraction          : 0.06
% 7.35/2.59  MUC search           : 0.00
% 7.35/2.59  Cooper               : 0.00
% 7.35/2.59  Total                : 1.86
% 7.35/2.59  Index Insertion      : 0.00
% 7.35/2.59  Index Deletion       : 0.00
% 7.35/2.59  Index Matching       : 0.00
% 7.35/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
