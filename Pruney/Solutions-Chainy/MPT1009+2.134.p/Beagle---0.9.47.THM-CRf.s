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
% DateTime   : Thu Dec  3 10:15:00 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 289 expanded)
%              Number of leaves         :   49 ( 117 expanded)
%              Depth                    :   15
%              Number of atoms          :  151 ( 547 expanded)
%              Number of equality atoms :   60 ( 142 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_137,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_125,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_99,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_52,plain,(
    ! [A_30,B_31] : v1_relat_1(k2_zfmisc_1(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_80,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_195,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_198,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_195])).

tff(c_204,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_198])).

tff(c_54,plain,(
    ! [B_33,A_32] :
      ( r1_tarski(k9_relat_1(B_33,A_32),k2_relat_1(B_33))
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_84,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_265,plain,(
    ! [C_82,A_83,B_84] :
      ( v4_relat_1(C_82,A_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_279,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_80,c_265])).

tff(c_58,plain,(
    ! [B_37,A_36] :
      ( k7_relat_1(B_37,A_36) = B_37
      | ~ v4_relat_1(B_37,A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_291,plain,
    ( k7_relat_1('#skF_6',k1_tarski('#skF_3')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_279,c_58])).

tff(c_294,plain,(
    k7_relat_1('#skF_6',k1_tarski('#skF_3')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_291])).

tff(c_355,plain,(
    ! [B_100,A_101] :
      ( k2_relat_1(k7_relat_1(B_100,A_101)) = k9_relat_1(B_100,A_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_367,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_355])).

tff(c_374,plain,(
    k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_367])).

tff(c_46,plain,(
    ! [A_25,B_27] :
      ( k9_relat_1(A_25,k1_tarski(B_27)) = k11_relat_1(A_25,B_27)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_416,plain,
    ( k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_46])).

tff(c_426,plain,(
    k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_416])).

tff(c_66,plain,(
    ! [A_38] :
      ( k1_relat_1(A_38) != k1_xboole_0
      | k1_xboole_0 = A_38
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_231,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_204,c_66])).

tff(c_234,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_340,plain,(
    ! [B_98,A_99] :
      ( r1_tarski(k1_relat_1(B_98),A_99)
      | ~ v4_relat_1(B_98,A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( k1_tarski(B_15) = A_14
      | k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_tarski(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_550,plain,(
    ! [B_138,B_139] :
      ( k1_tarski(B_138) = k1_relat_1(B_139)
      | k1_relat_1(B_139) = k1_xboole_0
      | ~ v4_relat_1(B_139,k1_tarski(B_138))
      | ~ v1_relat_1(B_139) ) ),
    inference(resolution,[status(thm)],[c_340,c_28])).

tff(c_553,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_279,c_550])).

tff(c_560,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_553])).

tff(c_561,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_560])).

tff(c_22,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_133,plain,(
    ! [D_55,B_56] : r2_hidden(D_55,k2_tarski(D_55,B_56)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_136,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_133])).

tff(c_593,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_136])).

tff(c_68,plain,(
    ! [B_40,A_39] :
      ( k1_tarski(k1_funct_1(B_40,A_39)) = k11_relat_1(B_40,A_39)
      | ~ r2_hidden(A_39,k1_relat_1(B_40))
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_615,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_593,c_68])).

tff(c_618,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_84,c_426,c_615])).

tff(c_507,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( k7_relset_1(A_121,B_122,C_123,D_124) = k9_relat_1(C_123,D_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_517,plain,(
    ! [D_124] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_124) = k9_relat_1('#skF_6',D_124) ),
    inference(resolution,[status(thm)],[c_80,c_507])).

tff(c_76,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_527,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_76])).

tff(c_669,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_527])).

tff(c_701,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_669])).

tff(c_705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_701])).

tff(c_706,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_719,plain,(
    ! [A_1] : r1_tarski('#skF_6',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_2])).

tff(c_60,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_717,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_706,c_60])).

tff(c_62,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_718,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_706,c_62])).

tff(c_888,plain,(
    ! [B_169,A_170] :
      ( v4_relat_1(B_169,A_170)
      | ~ r1_tarski(k1_relat_1(B_169),A_170)
      | ~ v1_relat_1(B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_894,plain,(
    ! [A_170] :
      ( v4_relat_1('#skF_6',A_170)
      | ~ r1_tarski('#skF_6',A_170)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_718,c_888])).

tff(c_897,plain,(
    ! [A_170] : v4_relat_1('#skF_6',A_170) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_719,c_894])).

tff(c_899,plain,(
    ! [B_172,A_173] :
      ( k7_relat_1(B_172,A_173) = B_172
      | ~ v4_relat_1(B_172,A_173)
      | ~ v1_relat_1(B_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_902,plain,(
    ! [A_170] :
      ( k7_relat_1('#skF_6',A_170) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_897,c_899])).

tff(c_906,plain,(
    ! [A_174] : k7_relat_1('#skF_6',A_174) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_902])).

tff(c_56,plain,(
    ! [B_35,A_34] :
      ( k2_relat_1(k7_relat_1(B_35,A_34)) = k9_relat_1(B_35,A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_911,plain,(
    ! [A_174] :
      ( k9_relat_1('#skF_6',A_174) = k2_relat_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_906,c_56])).

tff(c_916,plain,(
    ! [A_174] : k9_relat_1('#skF_6',A_174) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_717,c_911])).

tff(c_40,plain,(
    ! [A_18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_713,plain,(
    ! [A_18] : m1_subset_1('#skF_6',k1_zfmisc_1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_40])).

tff(c_1028,plain,(
    ! [A_198,B_199,C_200,D_201] :
      ( k7_relset_1(A_198,B_199,C_200,D_201) = k9_relat_1(C_200,D_201)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1031,plain,(
    ! [A_198,B_199,D_201] : k7_relset_1(A_198,B_199,'#skF_6',D_201) = k9_relat_1('#skF_6',D_201) ),
    inference(resolution,[status(thm)],[c_713,c_1028])).

tff(c_1037,plain,(
    ! [A_198,B_199,D_201] : k7_relset_1(A_198,B_199,'#skF_6',D_201) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_1031])).

tff(c_1038,plain,(
    ~ r1_tarski('#skF_6',k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1037,c_76])).

tff(c_1041,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1038])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:22:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.45  
% 3.10/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.45  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.10/1.45  
% 3.10/1.45  %Foreground sorts:
% 3.10/1.45  
% 3.10/1.45  
% 3.10/1.45  %Background operators:
% 3.10/1.45  
% 3.10/1.45  
% 3.10/1.45  %Foreground operators:
% 3.10/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.10/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.10/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.10/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.10/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.10/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.10/1.45  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.10/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.10/1.45  tff('#skF_5', type, '#skF_5': $i).
% 3.10/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.10/1.45  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.10/1.45  tff('#skF_6', type, '#skF_6': $i).
% 3.10/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.10/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.10/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.10/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.10/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.10/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.10/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.10/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.10/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.10/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.45  
% 3.21/1.47  tff(f_82, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.21/1.47  tff(f_137, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.21/1.47  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.21/1.47  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.21/1.47  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.21/1.47  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.21/1.47  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.21/1.47  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.21/1.47  tff(f_107, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.21/1.47  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.21/1.47  tff(f_48, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.21/1.47  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.21/1.47  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.21/1.47  tff(f_115, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 3.21/1.47  tff(f_125, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.21/1.47  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.21/1.47  tff(f_99, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.21/1.47  tff(f_56, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.21/1.47  tff(c_52, plain, (![A_30, B_31]: (v1_relat_1(k2_zfmisc_1(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.21/1.47  tff(c_80, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.21/1.47  tff(c_195, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.21/1.47  tff(c_198, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_195])).
% 3.21/1.47  tff(c_204, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_198])).
% 3.21/1.47  tff(c_54, plain, (![B_33, A_32]: (r1_tarski(k9_relat_1(B_33, A_32), k2_relat_1(B_33)) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.21/1.47  tff(c_84, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.21/1.47  tff(c_265, plain, (![C_82, A_83, B_84]: (v4_relat_1(C_82, A_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.21/1.47  tff(c_279, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_80, c_265])).
% 3.21/1.47  tff(c_58, plain, (![B_37, A_36]: (k7_relat_1(B_37, A_36)=B_37 | ~v4_relat_1(B_37, A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.21/1.47  tff(c_291, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_3'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_279, c_58])).
% 3.21/1.47  tff(c_294, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_3'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_204, c_291])).
% 3.21/1.47  tff(c_355, plain, (![B_100, A_101]: (k2_relat_1(k7_relat_1(B_100, A_101))=k9_relat_1(B_100, A_101) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.47  tff(c_367, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_294, c_355])).
% 3.21/1.47  tff(c_374, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_367])).
% 3.21/1.47  tff(c_46, plain, (![A_25, B_27]: (k9_relat_1(A_25, k1_tarski(B_27))=k11_relat_1(A_25, B_27) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.21/1.47  tff(c_416, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_374, c_46])).
% 3.21/1.47  tff(c_426, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_416])).
% 3.21/1.47  tff(c_66, plain, (![A_38]: (k1_relat_1(A_38)!=k1_xboole_0 | k1_xboole_0=A_38 | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.21/1.47  tff(c_231, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_204, c_66])).
% 3.21/1.47  tff(c_234, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_231])).
% 3.21/1.47  tff(c_340, plain, (![B_98, A_99]: (r1_tarski(k1_relat_1(B_98), A_99) | ~v4_relat_1(B_98, A_99) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.21/1.47  tff(c_28, plain, (![B_15, A_14]: (k1_tarski(B_15)=A_14 | k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_tarski(B_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.21/1.47  tff(c_550, plain, (![B_138, B_139]: (k1_tarski(B_138)=k1_relat_1(B_139) | k1_relat_1(B_139)=k1_xboole_0 | ~v4_relat_1(B_139, k1_tarski(B_138)) | ~v1_relat_1(B_139))), inference(resolution, [status(thm)], [c_340, c_28])).
% 3.21/1.47  tff(c_553, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_279, c_550])).
% 3.21/1.47  tff(c_560, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_204, c_553])).
% 3.21/1.47  tff(c_561, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_234, c_560])).
% 3.21/1.47  tff(c_22, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.21/1.47  tff(c_133, plain, (![D_55, B_56]: (r2_hidden(D_55, k2_tarski(D_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.21/1.47  tff(c_136, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_133])).
% 3.21/1.47  tff(c_593, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_561, c_136])).
% 3.21/1.47  tff(c_68, plain, (![B_40, A_39]: (k1_tarski(k1_funct_1(B_40, A_39))=k11_relat_1(B_40, A_39) | ~r2_hidden(A_39, k1_relat_1(B_40)) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.21/1.47  tff(c_615, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_593, c_68])).
% 3.21/1.47  tff(c_618, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_84, c_426, c_615])).
% 3.21/1.47  tff(c_507, plain, (![A_121, B_122, C_123, D_124]: (k7_relset_1(A_121, B_122, C_123, D_124)=k9_relat_1(C_123, D_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.21/1.47  tff(c_517, plain, (![D_124]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_124)=k9_relat_1('#skF_6', D_124))), inference(resolution, [status(thm)], [c_80, c_507])).
% 3.21/1.47  tff(c_76, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.21/1.47  tff(c_527, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_517, c_76])).
% 3.21/1.47  tff(c_669, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_618, c_527])).
% 3.21/1.47  tff(c_701, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_669])).
% 3.21/1.47  tff(c_705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_701])).
% 3.21/1.47  tff(c_706, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_231])).
% 3.21/1.47  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.21/1.47  tff(c_719, plain, (![A_1]: (r1_tarski('#skF_6', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_706, c_2])).
% 3.21/1.47  tff(c_60, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.21/1.47  tff(c_717, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_706, c_706, c_60])).
% 3.21/1.47  tff(c_62, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.21/1.47  tff(c_718, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_706, c_706, c_62])).
% 3.21/1.47  tff(c_888, plain, (![B_169, A_170]: (v4_relat_1(B_169, A_170) | ~r1_tarski(k1_relat_1(B_169), A_170) | ~v1_relat_1(B_169))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.21/1.47  tff(c_894, plain, (![A_170]: (v4_relat_1('#skF_6', A_170) | ~r1_tarski('#skF_6', A_170) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_718, c_888])).
% 3.21/1.47  tff(c_897, plain, (![A_170]: (v4_relat_1('#skF_6', A_170))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_719, c_894])).
% 3.21/1.47  tff(c_899, plain, (![B_172, A_173]: (k7_relat_1(B_172, A_173)=B_172 | ~v4_relat_1(B_172, A_173) | ~v1_relat_1(B_172))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.21/1.47  tff(c_902, plain, (![A_170]: (k7_relat_1('#skF_6', A_170)='#skF_6' | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_897, c_899])).
% 3.21/1.47  tff(c_906, plain, (![A_174]: (k7_relat_1('#skF_6', A_174)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_902])).
% 3.21/1.47  tff(c_56, plain, (![B_35, A_34]: (k2_relat_1(k7_relat_1(B_35, A_34))=k9_relat_1(B_35, A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.47  tff(c_911, plain, (![A_174]: (k9_relat_1('#skF_6', A_174)=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_906, c_56])).
% 3.21/1.47  tff(c_916, plain, (![A_174]: (k9_relat_1('#skF_6', A_174)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_717, c_911])).
% 3.21/1.47  tff(c_40, plain, (![A_18]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.21/1.47  tff(c_713, plain, (![A_18]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_706, c_40])).
% 3.21/1.47  tff(c_1028, plain, (![A_198, B_199, C_200, D_201]: (k7_relset_1(A_198, B_199, C_200, D_201)=k9_relat_1(C_200, D_201) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.21/1.47  tff(c_1031, plain, (![A_198, B_199, D_201]: (k7_relset_1(A_198, B_199, '#skF_6', D_201)=k9_relat_1('#skF_6', D_201))), inference(resolution, [status(thm)], [c_713, c_1028])).
% 3.21/1.47  tff(c_1037, plain, (![A_198, B_199, D_201]: (k7_relset_1(A_198, B_199, '#skF_6', D_201)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_916, c_1031])).
% 3.21/1.47  tff(c_1038, plain, (~r1_tarski('#skF_6', k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1037, c_76])).
% 3.21/1.47  tff(c_1041, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_719, c_1038])).
% 3.21/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.47  
% 3.21/1.47  Inference rules
% 3.21/1.47  ----------------------
% 3.21/1.47  #Ref     : 0
% 3.21/1.47  #Sup     : 203
% 3.21/1.47  #Fact    : 0
% 3.21/1.47  #Define  : 0
% 3.21/1.47  #Split   : 2
% 3.21/1.47  #Chain   : 0
% 3.21/1.47  #Close   : 0
% 3.21/1.47  
% 3.21/1.47  Ordering : KBO
% 3.21/1.47  
% 3.21/1.47  Simplification rules
% 3.21/1.47  ----------------------
% 3.21/1.47  #Subsume      : 4
% 3.21/1.47  #Demod        : 176
% 3.21/1.47  #Tautology    : 142
% 3.21/1.47  #SimpNegUnit  : 1
% 3.21/1.47  #BackRed      : 27
% 3.21/1.47  
% 3.21/1.47  #Partial instantiations: 0
% 3.21/1.47  #Strategies tried      : 1
% 3.21/1.47  
% 3.21/1.47  Timing (in seconds)
% 3.21/1.47  ----------------------
% 3.21/1.47  Preprocessing        : 0.34
% 3.21/1.47  Parsing              : 0.18
% 3.21/1.47  CNF conversion       : 0.02
% 3.21/1.47  Main loop            : 0.36
% 3.21/1.47  Inferencing          : 0.13
% 3.21/1.47  Reduction            : 0.12
% 3.21/1.47  Demodulation         : 0.09
% 3.21/1.47  BG Simplification    : 0.02
% 3.21/1.47  Subsumption          : 0.06
% 3.21/1.47  Abstraction          : 0.02
% 3.21/1.47  MUC search           : 0.00
% 3.21/1.47  Cooper               : 0.00
% 3.21/1.47  Total                : 0.73
% 3.21/1.47  Index Insertion      : 0.00
% 3.21/1.47  Index Deletion       : 0.00
% 3.21/1.47  Index Matching       : 0.00
% 3.21/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
