%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:54 EST 2020

% Result     : Theorem 6.62s
% Output     : CNFRefutation 6.68s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 165 expanded)
%              Number of leaves         :   40 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  157 ( 352 expanded)
%              Number of equality atoms :   31 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_68,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_134,axiom,(
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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_74,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_86,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_76,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_104,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_144,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_80,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_26,plain,(
    ! [B_19] : r1_tarski(B_19,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_76,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_7803,plain,(
    ! [C_481,A_482,B_483] :
      ( m1_subset_1(C_481,k1_zfmisc_1(k2_zfmisc_1(A_482,B_483)))
      | ~ r1_tarski(k2_relat_1(C_481),B_483)
      | ~ r1_tarski(k1_relat_1(C_481),A_482)
      | ~ v1_relat_1(C_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_82,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74])).

tff(c_122,plain,(
    ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_458,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_2'(A_91,B_92),A_91)
      | r1_tarski(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_468,plain,(
    ! [A_91,B_92] :
      ( ~ v1_xboole_0(A_91)
      | r1_tarski(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_458,c_4])).

tff(c_624,plain,(
    ! [B_107,A_108] :
      ( B_107 = A_108
      | ~ r1_tarski(B_107,A_108)
      | ~ r1_tarski(A_108,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_644,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_76,c_624])).

tff(c_672,plain,(
    ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_644])).

tff(c_676,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_468,c_672])).

tff(c_1892,plain,(
    ! [C_165,A_166,B_167] :
      ( m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ r1_tarski(k2_relat_1(C_165),B_167)
      | ~ r1_tarski(k1_relat_1(C_165),A_166)
      | ~ v1_relat_1(C_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5029,plain,(
    ! [C_321,A_322,B_323] :
      ( r1_tarski(C_321,k2_zfmisc_1(A_322,B_323))
      | ~ r1_tarski(k2_relat_1(C_321),B_323)
      | ~ r1_tarski(k1_relat_1(C_321),A_322)
      | ~ v1_relat_1(C_321) ) ),
    inference(resolution,[status(thm)],[c_1892,c_44])).

tff(c_5047,plain,(
    ! [A_322] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_322,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_322)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_76,c_5029])).

tff(c_5061,plain,(
    ! [A_324] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_324,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_324) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5047])).

tff(c_5105,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_5061])).

tff(c_46,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,k1_zfmisc_1(B_31))
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1461,plain,(
    ! [A_151,B_152,C_153] :
      ( k1_relset_1(A_151,B_152,C_153) = k1_relat_1(C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1476,plain,(
    ! [A_151,B_152,A_30] :
      ( k1_relset_1(A_151,B_152,A_30) = k1_relat_1(A_30)
      | ~ r1_tarski(A_30,k2_zfmisc_1(A_151,B_152)) ) ),
    inference(resolution,[status(thm)],[c_46,c_1461])).

tff(c_5158,plain,(
    k1_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5105,c_1476])).

tff(c_2372,plain,(
    ! [B_186,C_187,A_188] :
      ( k1_xboole_0 = B_186
      | v1_funct_2(C_187,A_188,B_186)
      | k1_relset_1(A_188,B_186,C_187) != A_188
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_188,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_5668,plain,(
    ! [B_339,A_340,A_341] :
      ( k1_xboole_0 = B_339
      | v1_funct_2(A_340,A_341,B_339)
      | k1_relset_1(A_341,B_339,A_340) != A_341
      | ~ r1_tarski(A_340,k2_zfmisc_1(A_341,B_339)) ) ),
    inference(resolution,[status(thm)],[c_46,c_2372])).

tff(c_5677,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_4')
    | k1_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') != k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5105,c_5668])).

tff(c_5731,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5158,c_5677])).

tff(c_5732,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_5731])).

tff(c_144,plain,(
    ! [B_57,A_58] : k2_xboole_0(B_57,A_58) = k2_xboole_0(A_58,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_22] : k2_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_197,plain,(
    ! [A_59] : k2_xboole_0(k1_xboole_0,A_59) = A_59 ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_30])).

tff(c_36,plain,(
    ! [A_26,B_27] : r1_tarski(A_26,k2_xboole_0(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_209,plain,(
    ! [A_59] : r1_tarski(k1_xboole_0,A_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_36])).

tff(c_32,plain,(
    ! [A_23] : r1_xboole_0(A_23,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    ! [A_33] :
      ( v1_xboole_0(k1_relat_1(A_33))
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_129,plain,(
    ! [A_54] :
      ( v1_xboole_0(k1_relat_1(A_54))
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_14,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_134,plain,(
    ! [A_55] :
      ( k1_relat_1(A_55) = k1_xboole_0
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_129,c_14])).

tff(c_358,plain,(
    ! [A_68] :
      ( k1_relat_1(k1_relat_1(A_68)) = k1_xboole_0
      | ~ v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_50,c_134])).

tff(c_367,plain,(
    ! [A_68] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_68))
      | ~ v1_xboole_0(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_50])).

tff(c_388,plain,(
    ! [A_75] :
      ( ~ v1_xboole_0(k1_relat_1(A_75))
      | ~ v1_xboole_0(A_75) ) ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_395,plain,(
    ! [A_33] : ~ v1_xboole_0(A_33) ),
    inference(resolution,[status(thm)],[c_50,c_388])).

tff(c_34,plain,(
    ! [B_25,A_24] :
      ( ~ r1_xboole_0(B_25,A_24)
      | ~ r1_tarski(B_25,A_24)
      | v1_xboole_0(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_402,plain,(
    ! [B_80,A_81] :
      ( ~ r1_xboole_0(B_80,A_81)
      | ~ r1_tarski(B_80,A_81) ) ),
    inference(negUnitSimplification,[status(thm)],[c_395,c_34])).

tff(c_407,plain,(
    ! [A_82] : ~ r1_tarski(A_82,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_402])).

tff(c_415,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_209,c_407])).

tff(c_416,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_5778,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5732,c_416])).

tff(c_5789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_676,c_5778])).

tff(c_5790,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_644])).

tff(c_6184,plain,(
    ! [A_368] :
      ( v1_funct_2(A_368,k1_relat_1(A_368),k2_relat_1(A_368))
      | ~ v1_funct_1(A_368)
      | ~ v1_relat_1(A_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_6187,plain,
    ( v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5790,c_6184])).

tff(c_6195,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_6187])).

tff(c_6197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_6195])).

tff(c_6198,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_7809,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_7803,c_6198])).

tff(c_7823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_26,c_76,c_7809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.62/2.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.62/2.38  
% 6.62/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.68/2.38  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 6.68/2.38  
% 6.68/2.38  %Foreground sorts:
% 6.68/2.38  
% 6.68/2.38  
% 6.68/2.38  %Background operators:
% 6.68/2.38  
% 6.68/2.38  
% 6.68/2.38  %Foreground operators:
% 6.68/2.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.68/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.68/2.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.68/2.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.68/2.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.68/2.38  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 6.68/2.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.68/2.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.68/2.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.68/2.38  tff('#skF_5', type, '#skF_5': $i).
% 6.68/2.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.68/2.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.68/2.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.68/2.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.68/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.68/2.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.68/2.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.68/2.38  tff('#skF_4', type, '#skF_4': $i).
% 6.68/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.68/2.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.68/2.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.68/2.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.68/2.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.68/2.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.68/2.38  
% 6.68/2.40  tff(f_157, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 6.68/2.40  tff(f_68, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.68/2.40  tff(f_116, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 6.68/2.40  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.68/2.40  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.68/2.40  tff(f_96, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.68/2.40  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.68/2.40  tff(f_134, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.68/2.40  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.68/2.40  tff(f_74, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 6.68/2.40  tff(f_86, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.68/2.40  tff(f_76, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 6.68/2.40  tff(f_104, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 6.68/2.40  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.68/2.40  tff(f_84, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 6.68/2.40  tff(f_144, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 6.68/2.40  tff(c_80, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.68/2.40  tff(c_26, plain, (![B_19]: (r1_tarski(B_19, B_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.68/2.40  tff(c_76, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.68/2.40  tff(c_7803, plain, (![C_481, A_482, B_483]: (m1_subset_1(C_481, k1_zfmisc_1(k2_zfmisc_1(A_482, B_483))) | ~r1_tarski(k2_relat_1(C_481), B_483) | ~r1_tarski(k1_relat_1(C_481), A_482) | ~v1_relat_1(C_481))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.68/2.40  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.68/2.40  tff(c_74, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.68/2.40  tff(c_82, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74])).
% 6.68/2.40  tff(c_122, plain, (~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_82])).
% 6.68/2.40  tff(c_458, plain, (![A_91, B_92]: (r2_hidden('#skF_2'(A_91, B_92), A_91) | r1_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.68/2.40  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.68/2.40  tff(c_468, plain, (![A_91, B_92]: (~v1_xboole_0(A_91) | r1_tarski(A_91, B_92))), inference(resolution, [status(thm)], [c_458, c_4])).
% 6.68/2.40  tff(c_624, plain, (![B_107, A_108]: (B_107=A_108 | ~r1_tarski(B_107, A_108) | ~r1_tarski(A_108, B_107))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.68/2.40  tff(c_644, plain, (k2_relat_1('#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_624])).
% 6.68/2.40  tff(c_672, plain, (~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_644])).
% 6.68/2.40  tff(c_676, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_468, c_672])).
% 6.68/2.40  tff(c_1892, plain, (![C_165, A_166, B_167]: (m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~r1_tarski(k2_relat_1(C_165), B_167) | ~r1_tarski(k1_relat_1(C_165), A_166) | ~v1_relat_1(C_165))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.68/2.40  tff(c_44, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | ~m1_subset_1(A_30, k1_zfmisc_1(B_31)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.68/2.40  tff(c_5029, plain, (![C_321, A_322, B_323]: (r1_tarski(C_321, k2_zfmisc_1(A_322, B_323)) | ~r1_tarski(k2_relat_1(C_321), B_323) | ~r1_tarski(k1_relat_1(C_321), A_322) | ~v1_relat_1(C_321))), inference(resolution, [status(thm)], [c_1892, c_44])).
% 6.68/2.40  tff(c_5047, plain, (![A_322]: (r1_tarski('#skF_5', k2_zfmisc_1(A_322, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), A_322) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_5029])).
% 6.68/2.40  tff(c_5061, plain, (![A_324]: (r1_tarski('#skF_5', k2_zfmisc_1(A_324, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), A_324))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_5047])).
% 6.68/2.40  tff(c_5105, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_5061])).
% 6.68/2.40  tff(c_46, plain, (![A_30, B_31]: (m1_subset_1(A_30, k1_zfmisc_1(B_31)) | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.68/2.40  tff(c_1461, plain, (![A_151, B_152, C_153]: (k1_relset_1(A_151, B_152, C_153)=k1_relat_1(C_153) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.68/2.40  tff(c_1476, plain, (![A_151, B_152, A_30]: (k1_relset_1(A_151, B_152, A_30)=k1_relat_1(A_30) | ~r1_tarski(A_30, k2_zfmisc_1(A_151, B_152)))), inference(resolution, [status(thm)], [c_46, c_1461])).
% 6.68/2.40  tff(c_5158, plain, (k1_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_5105, c_1476])).
% 6.68/2.40  tff(c_2372, plain, (![B_186, C_187, A_188]: (k1_xboole_0=B_186 | v1_funct_2(C_187, A_188, B_186) | k1_relset_1(A_188, B_186, C_187)!=A_188 | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_188, B_186))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.68/2.40  tff(c_5668, plain, (![B_339, A_340, A_341]: (k1_xboole_0=B_339 | v1_funct_2(A_340, A_341, B_339) | k1_relset_1(A_341, B_339, A_340)!=A_341 | ~r1_tarski(A_340, k2_zfmisc_1(A_341, B_339)))), inference(resolution, [status(thm)], [c_46, c_2372])).
% 6.68/2.40  tff(c_5677, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_4') | k1_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')!=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_5105, c_5668])).
% 6.68/2.40  tff(c_5731, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5158, c_5677])).
% 6.68/2.40  tff(c_5732, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_122, c_5731])).
% 6.68/2.40  tff(c_144, plain, (![B_57, A_58]: (k2_xboole_0(B_57, A_58)=k2_xboole_0(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.68/2.40  tff(c_30, plain, (![A_22]: (k2_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.68/2.40  tff(c_197, plain, (![A_59]: (k2_xboole_0(k1_xboole_0, A_59)=A_59)), inference(superposition, [status(thm), theory('equality')], [c_144, c_30])).
% 6.68/2.40  tff(c_36, plain, (![A_26, B_27]: (r1_tarski(A_26, k2_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.68/2.40  tff(c_209, plain, (![A_59]: (r1_tarski(k1_xboole_0, A_59))), inference(superposition, [status(thm), theory('equality')], [c_197, c_36])).
% 6.68/2.40  tff(c_32, plain, (![A_23]: (r1_xboole_0(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.68/2.40  tff(c_50, plain, (![A_33]: (v1_xboole_0(k1_relat_1(A_33)) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.68/2.40  tff(c_129, plain, (![A_54]: (v1_xboole_0(k1_relat_1(A_54)) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.68/2.40  tff(c_14, plain, (![A_12]: (k1_xboole_0=A_12 | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.68/2.40  tff(c_134, plain, (![A_55]: (k1_relat_1(A_55)=k1_xboole_0 | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_129, c_14])).
% 6.68/2.40  tff(c_358, plain, (![A_68]: (k1_relat_1(k1_relat_1(A_68))=k1_xboole_0 | ~v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_50, c_134])).
% 6.68/2.40  tff(c_367, plain, (![A_68]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_68)) | ~v1_xboole_0(A_68))), inference(superposition, [status(thm), theory('equality')], [c_358, c_50])).
% 6.68/2.40  tff(c_388, plain, (![A_75]: (~v1_xboole_0(k1_relat_1(A_75)) | ~v1_xboole_0(A_75))), inference(splitLeft, [status(thm)], [c_367])).
% 6.68/2.40  tff(c_395, plain, (![A_33]: (~v1_xboole_0(A_33))), inference(resolution, [status(thm)], [c_50, c_388])).
% 6.68/2.40  tff(c_34, plain, (![B_25, A_24]: (~r1_xboole_0(B_25, A_24) | ~r1_tarski(B_25, A_24) | v1_xboole_0(B_25))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.68/2.40  tff(c_402, plain, (![B_80, A_81]: (~r1_xboole_0(B_80, A_81) | ~r1_tarski(B_80, A_81))), inference(negUnitSimplification, [status(thm)], [c_395, c_34])).
% 6.68/2.40  tff(c_407, plain, (![A_82]: (~r1_tarski(A_82, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_402])).
% 6.68/2.40  tff(c_415, plain, $false, inference(resolution, [status(thm)], [c_209, c_407])).
% 6.68/2.40  tff(c_416, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_367])).
% 6.68/2.40  tff(c_5778, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5732, c_416])).
% 6.68/2.40  tff(c_5789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_676, c_5778])).
% 6.68/2.40  tff(c_5790, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_644])).
% 6.68/2.40  tff(c_6184, plain, (![A_368]: (v1_funct_2(A_368, k1_relat_1(A_368), k2_relat_1(A_368)) | ~v1_funct_1(A_368) | ~v1_relat_1(A_368))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.68/2.40  tff(c_6187, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5790, c_6184])).
% 6.68/2.40  tff(c_6195, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_6187])).
% 6.68/2.40  tff(c_6197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_6195])).
% 6.68/2.40  tff(c_6198, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')))), inference(splitRight, [status(thm)], [c_82])).
% 6.68/2.40  tff(c_7809, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_7803, c_6198])).
% 6.68/2.40  tff(c_7823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_26, c_76, c_7809])).
% 6.68/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.68/2.40  
% 6.68/2.40  Inference rules
% 6.68/2.40  ----------------------
% 6.68/2.40  #Ref     : 0
% 6.68/2.40  #Sup     : 1907
% 6.68/2.40  #Fact    : 0
% 6.68/2.40  #Define  : 0
% 6.68/2.40  #Split   : 17
% 6.68/2.40  #Chain   : 0
% 6.68/2.40  #Close   : 0
% 6.68/2.40  
% 6.68/2.40  Ordering : KBO
% 6.68/2.40  
% 6.68/2.40  Simplification rules
% 6.68/2.40  ----------------------
% 6.68/2.40  #Subsume      : 771
% 6.68/2.40  #Demod        : 1171
% 6.68/2.40  #Tautology    : 710
% 6.68/2.40  #SimpNegUnit  : 49
% 6.68/2.40  #BackRed      : 57
% 6.68/2.40  
% 6.68/2.40  #Partial instantiations: 0
% 6.68/2.40  #Strategies tried      : 1
% 6.68/2.40  
% 6.68/2.40  Timing (in seconds)
% 6.68/2.40  ----------------------
% 6.68/2.40  Preprocessing        : 0.40
% 6.68/2.40  Parsing              : 0.20
% 6.68/2.40  CNF conversion       : 0.03
% 6.68/2.40  Main loop            : 1.18
% 6.68/2.40  Inferencing          : 0.35
% 6.68/2.40  Reduction            : 0.45
% 6.68/2.40  Demodulation         : 0.35
% 6.68/2.40  BG Simplification    : 0.04
% 6.68/2.40  Subsumption          : 0.25
% 6.68/2.40  Abstraction          : 0.05
% 6.68/2.40  MUC search           : 0.00
% 6.68/2.40  Cooper               : 0.00
% 6.68/2.40  Total                : 1.62
% 6.68/2.40  Index Insertion      : 0.00
% 6.68/2.40  Index Deletion       : 0.00
% 6.68/2.40  Index Matching       : 0.00
% 6.68/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
