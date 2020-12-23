%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:45 EST 2020

% Result     : Theorem 5.33s
% Output     : CNFRefutation 5.45s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 515 expanded)
%              Number of leaves         :   29 ( 184 expanded)
%              Depth                    :   12
%              Number of atoms          :  164 (1091 expanded)
%              Number of equality atoms :   43 ( 227 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_38,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
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

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_47,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_3993,plain,(
    ! [A_294,B_295] :
      ( r1_tarski(A_294,B_295)
      | ~ m1_subset_1(A_294,k1_zfmisc_1(B_295)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4001,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_47,c_3993])).

tff(c_4333,plain,(
    ! [C_332,A_333,B_334] :
      ( m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_333,B_334)))
      | ~ r1_tarski(k2_relat_1(C_332),B_334)
      | ~ r1_tarski(k1_relat_1(C_332),A_333)
      | ~ v1_relat_1(C_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_144,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_152,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_47,c_144])).

tff(c_479,plain,(
    ! [C_75,A_76,B_77] :
      ( m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ r1_tarski(k2_relat_1(C_75),B_77)
      | ~ r1_tarski(k1_relat_1(C_75),A_76)
      | ~ v1_relat_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1349,plain,(
    ! [C_149,A_150,B_151] :
      ( r1_tarski(C_149,k2_zfmisc_1(A_150,B_151))
      | ~ r1_tarski(k2_relat_1(C_149),B_151)
      | ~ r1_tarski(k1_relat_1(C_149),A_150)
      | ~ v1_relat_1(C_149) ) ),
    inference(resolution,[status(thm)],[c_479,c_16])).

tff(c_1354,plain,(
    ! [C_152,A_153] :
      ( r1_tarski(C_152,k2_zfmisc_1(A_153,k2_relat_1(C_152)))
      | ~ r1_tarski(k1_relat_1(C_152),A_153)
      | ~ v1_relat_1(C_152) ) ),
    inference(resolution,[status(thm)],[c_152,c_1349])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_363,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_relset_1(A_56,B_57,C_58) = k1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_384,plain,(
    ! [A_56,B_57,A_6] :
      ( k1_relset_1(A_56,B_57,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_56,B_57)) ) ),
    inference(resolution,[status(thm)],[c_18,c_363])).

tff(c_1398,plain,(
    ! [A_155,C_156] :
      ( k1_relset_1(A_155,k2_relat_1(C_156),C_156) = k1_relat_1(C_156)
      | ~ r1_tarski(k1_relat_1(C_156),A_155)
      | ~ v1_relat_1(C_156) ) ),
    inference(resolution,[status(thm)],[c_1354,c_384])).

tff(c_1417,plain,(
    ! [C_156] :
      ( k1_relset_1(k1_relat_1(C_156),k2_relat_1(C_156),C_156) = k1_relat_1(C_156)
      | ~ v1_relat_1(C_156) ) ),
    inference(resolution,[status(thm)],[c_152,c_1398])).

tff(c_26,plain,(
    ! [C_18,A_16,B_17] :
      ( m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ r1_tarski(k2_relat_1(C_18),B_17)
      | ~ r1_tarski(k1_relat_1(C_18),A_16)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_728,plain,(
    ! [B_96,C_97,A_98] :
      ( k1_xboole_0 = B_96
      | v1_funct_2(C_97,A_98,B_96)
      | k1_relset_1(A_98,B_96,C_97) != A_98
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3027,plain,(
    ! [B_251,C_252,A_253] :
      ( k1_xboole_0 = B_251
      | v1_funct_2(C_252,A_253,B_251)
      | k1_relset_1(A_253,B_251,C_252) != A_253
      | ~ r1_tarski(k2_relat_1(C_252),B_251)
      | ~ r1_tarski(k1_relat_1(C_252),A_253)
      | ~ v1_relat_1(C_252) ) ),
    inference(resolution,[status(thm)],[c_26,c_728])).

tff(c_3685,plain,(
    ! [C_285,A_286] :
      ( k2_relat_1(C_285) = k1_xboole_0
      | v1_funct_2(C_285,A_286,k2_relat_1(C_285))
      | k1_relset_1(A_286,k2_relat_1(C_285),C_285) != A_286
      | ~ r1_tarski(k1_relat_1(C_285),A_286)
      | ~ v1_relat_1(C_285) ) ),
    inference(resolution,[status(thm)],[c_152,c_3027])).

tff(c_42,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40])).

tff(c_97,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_3697,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3685,c_97])).

tff(c_3705,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_152,c_3697])).

tff(c_3706,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3705])).

tff(c_3709,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1417,c_3706])).

tff(c_3713,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3709])).

tff(c_3714,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3705])).

tff(c_22,plain,(
    ! [C_12,B_10,A_9] :
      ( v1_xboole_0(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(B_10,A_9)))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1044,plain,(
    ! [C_119,B_120,A_121] :
      ( v1_xboole_0(C_119)
      | ~ v1_xboole_0(B_120)
      | ~ r1_tarski(k2_relat_1(C_119),B_120)
      | ~ r1_tarski(k1_relat_1(C_119),A_121)
      | ~ v1_relat_1(C_119) ) ),
    inference(resolution,[status(thm)],[c_479,c_22])).

tff(c_1049,plain,(
    ! [C_122,A_123] :
      ( v1_xboole_0(C_122)
      | ~ v1_xboole_0(k2_relat_1(C_122))
      | ~ r1_tarski(k1_relat_1(C_122),A_123)
      | ~ v1_relat_1(C_122) ) ),
    inference(resolution,[status(thm)],[c_152,c_1044])).

tff(c_1065,plain,(
    ! [C_122] :
      ( v1_xboole_0(C_122)
      | ~ v1_xboole_0(k2_relat_1(C_122))
      | ~ v1_relat_1(C_122) ) ),
    inference(resolution,[status(thm)],[c_152,c_1049])).

tff(c_3737,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3714,c_1065])).

tff(c_3757,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2,c_3737])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_3771,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3757,c_4])).

tff(c_92,plain,(
    ! [A_27] :
      ( v1_xboole_0(k1_relat_1(A_27))
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_98,plain,(
    ! [A_28] :
      ( k1_relat_1(A_28) = k1_xboole_0
      | ~ v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_92,c_4])).

tff(c_106,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_98])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_406,plain,(
    ! [B_62,C_63] :
      ( k1_relset_1(k1_xboole_0,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_363])).

tff(c_412,plain,(
    ! [B_62] : k1_relset_1(k1_xboole_0,B_62,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_47,c_406])).

tff(c_415,plain,(
    ! [B_62] : k1_relset_1(k1_xboole_0,B_62,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_412])).

tff(c_32,plain,(
    ! [C_21,B_20] :
      ( v1_funct_2(C_21,k1_xboole_0,B_20)
      | k1_relset_1(k1_xboole_0,B_20,C_21) != k1_xboole_0
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_439,plain,(
    ! [C_69,B_70] :
      ( v1_funct_2(C_69,k1_xboole_0,B_70)
      | k1_relset_1(k1_xboole_0,B_70,C_69) != k1_xboole_0
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_32])).

tff(c_445,plain,(
    ! [B_70] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_70)
      | k1_relset_1(k1_xboole_0,B_70,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_47,c_439])).

tff(c_449,plain,(
    ! [B_70] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_445])).

tff(c_3821,plain,(
    ! [B_70] : v1_funct_2('#skF_1','#skF_1',B_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3771,c_3771,c_449])).

tff(c_96,plain,(
    ! [A_27] :
      ( k1_relat_1(A_27) = k1_xboole_0
      | ~ v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_92,c_4])).

tff(c_3770,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3757,c_96])).

tff(c_3849,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3771,c_3770])).

tff(c_3716,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3714,c_97])).

tff(c_3772,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3771,c_3716])).

tff(c_3944,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3821,c_3849,c_3772])).

tff(c_3945,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_4342,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4333,c_3945])).

tff(c_4363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4001,c_4001,c_4342])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.33/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.11  
% 5.33/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.11  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 5.33/2.11  
% 5.33/2.11  %Foreground sorts:
% 5.33/2.11  
% 5.33/2.11  
% 5.33/2.11  %Background operators:
% 5.33/2.11  
% 5.33/2.11  
% 5.33/2.11  %Foreground operators:
% 5.33/2.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.33/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.33/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.33/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.33/2.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.33/2.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.33/2.11  tff('#skF_1', type, '#skF_1': $i).
% 5.33/2.11  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.33/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.33/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.33/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.33/2.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.33/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.33/2.11  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.33/2.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.33/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.33/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.33/2.11  
% 5.45/2.12  tff(f_96, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 5.45/2.12  tff(f_38, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.45/2.12  tff(f_40, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.45/2.12  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.45/2.12  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 5.45/2.12  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.45/2.13  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.45/2.13  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.45/2.13  tff(f_55, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.45/2.13  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.45/2.13  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 5.45/2.13  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.45/2.13  tff(c_44, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.45/2.13  tff(c_12, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.45/2.13  tff(c_14, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.45/2.13  tff(c_47, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 5.45/2.13  tff(c_3993, plain, (![A_294, B_295]: (r1_tarski(A_294, B_295) | ~m1_subset_1(A_294, k1_zfmisc_1(B_295)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.45/2.13  tff(c_4001, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_47, c_3993])).
% 5.45/2.13  tff(c_4333, plain, (![C_332, A_333, B_334]: (m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_333, B_334))) | ~r1_tarski(k2_relat_1(C_332), B_334) | ~r1_tarski(k1_relat_1(C_332), A_333) | ~v1_relat_1(C_332))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.45/2.13  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.45/2.13  tff(c_144, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.45/2.13  tff(c_152, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_47, c_144])).
% 5.45/2.13  tff(c_479, plain, (![C_75, A_76, B_77]: (m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~r1_tarski(k2_relat_1(C_75), B_77) | ~r1_tarski(k1_relat_1(C_75), A_76) | ~v1_relat_1(C_75))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.45/2.13  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.45/2.13  tff(c_1349, plain, (![C_149, A_150, B_151]: (r1_tarski(C_149, k2_zfmisc_1(A_150, B_151)) | ~r1_tarski(k2_relat_1(C_149), B_151) | ~r1_tarski(k1_relat_1(C_149), A_150) | ~v1_relat_1(C_149))), inference(resolution, [status(thm)], [c_479, c_16])).
% 5.45/2.13  tff(c_1354, plain, (![C_152, A_153]: (r1_tarski(C_152, k2_zfmisc_1(A_153, k2_relat_1(C_152))) | ~r1_tarski(k1_relat_1(C_152), A_153) | ~v1_relat_1(C_152))), inference(resolution, [status(thm)], [c_152, c_1349])).
% 5.45/2.13  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.45/2.13  tff(c_363, plain, (![A_56, B_57, C_58]: (k1_relset_1(A_56, B_57, C_58)=k1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.45/2.13  tff(c_384, plain, (![A_56, B_57, A_6]: (k1_relset_1(A_56, B_57, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_56, B_57)))), inference(resolution, [status(thm)], [c_18, c_363])).
% 5.45/2.13  tff(c_1398, plain, (![A_155, C_156]: (k1_relset_1(A_155, k2_relat_1(C_156), C_156)=k1_relat_1(C_156) | ~r1_tarski(k1_relat_1(C_156), A_155) | ~v1_relat_1(C_156))), inference(resolution, [status(thm)], [c_1354, c_384])).
% 5.45/2.13  tff(c_1417, plain, (![C_156]: (k1_relset_1(k1_relat_1(C_156), k2_relat_1(C_156), C_156)=k1_relat_1(C_156) | ~v1_relat_1(C_156))), inference(resolution, [status(thm)], [c_152, c_1398])).
% 5.45/2.13  tff(c_26, plain, (![C_18, A_16, B_17]: (m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | ~r1_tarski(k2_relat_1(C_18), B_17) | ~r1_tarski(k1_relat_1(C_18), A_16) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.45/2.13  tff(c_728, plain, (![B_96, C_97, A_98]: (k1_xboole_0=B_96 | v1_funct_2(C_97, A_98, B_96) | k1_relset_1(A_98, B_96, C_97)!=A_98 | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_96))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.45/2.13  tff(c_3027, plain, (![B_251, C_252, A_253]: (k1_xboole_0=B_251 | v1_funct_2(C_252, A_253, B_251) | k1_relset_1(A_253, B_251, C_252)!=A_253 | ~r1_tarski(k2_relat_1(C_252), B_251) | ~r1_tarski(k1_relat_1(C_252), A_253) | ~v1_relat_1(C_252))), inference(resolution, [status(thm)], [c_26, c_728])).
% 5.45/2.13  tff(c_3685, plain, (![C_285, A_286]: (k2_relat_1(C_285)=k1_xboole_0 | v1_funct_2(C_285, A_286, k2_relat_1(C_285)) | k1_relset_1(A_286, k2_relat_1(C_285), C_285)!=A_286 | ~r1_tarski(k1_relat_1(C_285), A_286) | ~v1_relat_1(C_285))), inference(resolution, [status(thm)], [c_152, c_3027])).
% 5.45/2.13  tff(c_42, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.45/2.13  tff(c_40, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.45/2.13  tff(c_46, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40])).
% 5.45/2.13  tff(c_97, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_46])).
% 5.45/2.13  tff(c_3697, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3685, c_97])).
% 5.45/2.13  tff(c_3705, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_152, c_3697])).
% 5.45/2.13  tff(c_3706, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_3705])).
% 5.45/2.13  tff(c_3709, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1417, c_3706])).
% 5.45/2.13  tff(c_3713, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_3709])).
% 5.45/2.13  tff(c_3714, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3705])).
% 5.45/2.13  tff(c_22, plain, (![C_12, B_10, A_9]: (v1_xboole_0(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(B_10, A_9))) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.45/2.13  tff(c_1044, plain, (![C_119, B_120, A_121]: (v1_xboole_0(C_119) | ~v1_xboole_0(B_120) | ~r1_tarski(k2_relat_1(C_119), B_120) | ~r1_tarski(k1_relat_1(C_119), A_121) | ~v1_relat_1(C_119))), inference(resolution, [status(thm)], [c_479, c_22])).
% 5.45/2.13  tff(c_1049, plain, (![C_122, A_123]: (v1_xboole_0(C_122) | ~v1_xboole_0(k2_relat_1(C_122)) | ~r1_tarski(k1_relat_1(C_122), A_123) | ~v1_relat_1(C_122))), inference(resolution, [status(thm)], [c_152, c_1044])).
% 5.45/2.13  tff(c_1065, plain, (![C_122]: (v1_xboole_0(C_122) | ~v1_xboole_0(k2_relat_1(C_122)) | ~v1_relat_1(C_122))), inference(resolution, [status(thm)], [c_152, c_1049])).
% 5.45/2.13  tff(c_3737, plain, (v1_xboole_0('#skF_1') | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3714, c_1065])).
% 5.45/2.13  tff(c_3757, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2, c_3737])).
% 5.45/2.13  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.45/2.13  tff(c_3771, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_3757, c_4])).
% 5.45/2.13  tff(c_92, plain, (![A_27]: (v1_xboole_0(k1_relat_1(A_27)) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.45/2.13  tff(c_98, plain, (![A_28]: (k1_relat_1(A_28)=k1_xboole_0 | ~v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_92, c_4])).
% 5.45/2.13  tff(c_106, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_98])).
% 5.45/2.13  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.45/2.13  tff(c_406, plain, (![B_62, C_63]: (k1_relset_1(k1_xboole_0, B_62, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_363])).
% 5.45/2.13  tff(c_412, plain, (![B_62]: (k1_relset_1(k1_xboole_0, B_62, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_47, c_406])).
% 5.45/2.13  tff(c_415, plain, (![B_62]: (k1_relset_1(k1_xboole_0, B_62, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_412])).
% 5.45/2.13  tff(c_32, plain, (![C_21, B_20]: (v1_funct_2(C_21, k1_xboole_0, B_20) | k1_relset_1(k1_xboole_0, B_20, C_21)!=k1_xboole_0 | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_20))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.45/2.13  tff(c_439, plain, (![C_69, B_70]: (v1_funct_2(C_69, k1_xboole_0, B_70) | k1_relset_1(k1_xboole_0, B_70, C_69)!=k1_xboole_0 | ~m1_subset_1(C_69, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_32])).
% 5.45/2.13  tff(c_445, plain, (![B_70]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_70) | k1_relset_1(k1_xboole_0, B_70, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_47, c_439])).
% 5.45/2.13  tff(c_449, plain, (![B_70]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_70))), inference(demodulation, [status(thm), theory('equality')], [c_415, c_445])).
% 5.45/2.13  tff(c_3821, plain, (![B_70]: (v1_funct_2('#skF_1', '#skF_1', B_70))), inference(demodulation, [status(thm), theory('equality')], [c_3771, c_3771, c_449])).
% 5.45/2.13  tff(c_96, plain, (![A_27]: (k1_relat_1(A_27)=k1_xboole_0 | ~v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_92, c_4])).
% 5.45/2.13  tff(c_3770, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_3757, c_96])).
% 5.45/2.13  tff(c_3849, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3771, c_3770])).
% 5.45/2.13  tff(c_3716, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3714, c_97])).
% 5.45/2.13  tff(c_3772, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3771, c_3716])).
% 5.45/2.13  tff(c_3944, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3821, c_3849, c_3772])).
% 5.45/2.13  tff(c_3945, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_46])).
% 5.45/2.13  tff(c_4342, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4333, c_3945])).
% 5.45/2.13  tff(c_4363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_4001, c_4001, c_4342])).
% 5.45/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.45/2.13  
% 5.45/2.13  Inference rules
% 5.45/2.13  ----------------------
% 5.45/2.13  #Ref     : 0
% 5.45/2.13  #Sup     : 1019
% 5.45/2.13  #Fact    : 0
% 5.45/2.13  #Define  : 0
% 5.45/2.13  #Split   : 4
% 5.45/2.13  #Chain   : 0
% 5.45/2.13  #Close   : 0
% 5.45/2.13  
% 5.45/2.13  Ordering : KBO
% 5.45/2.13  
% 5.45/2.13  Simplification rules
% 5.45/2.13  ----------------------
% 5.45/2.13  #Subsume      : 237
% 5.45/2.13  #Demod        : 1137
% 5.45/2.13  #Tautology    : 475
% 5.45/2.13  #SimpNegUnit  : 0
% 5.45/2.13  #BackRed      : 147
% 5.45/2.13  
% 5.45/2.13  #Partial instantiations: 0
% 5.45/2.13  #Strategies tried      : 1
% 5.45/2.13  
% 5.45/2.13  Timing (in seconds)
% 5.45/2.13  ----------------------
% 5.45/2.13  Preprocessing        : 0.32
% 5.45/2.13  Parsing              : 0.16
% 5.45/2.13  CNF conversion       : 0.02
% 5.45/2.13  Main loop            : 0.90
% 5.45/2.13  Inferencing          : 0.30
% 5.45/2.13  Reduction            : 0.29
% 5.45/2.13  Demodulation         : 0.21
% 5.45/2.13  BG Simplification    : 0.04
% 5.45/2.13  Subsumption          : 0.21
% 5.45/2.13  Abstraction          : 0.05
% 5.45/2.13  MUC search           : 0.00
% 5.45/2.13  Cooper               : 0.00
% 5.45/2.13  Total                : 1.26
% 5.45/2.13  Index Insertion      : 0.00
% 5.45/2.13  Index Deletion       : 0.00
% 5.45/2.13  Index Matching       : 0.00
% 5.45/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
