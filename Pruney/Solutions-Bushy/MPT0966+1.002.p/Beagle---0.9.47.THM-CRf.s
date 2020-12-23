%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0966+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:09 EST 2020

% Result     : Theorem 5.16s
% Output     : CNFRefutation 5.51s
% Verified   : 
% Statistics : Number of formulae       :  254 (1502 expanded)
%              Number of leaves         :   33 ( 478 expanded)
%              Depth                    :   14
%              Number of atoms          :  439 (4523 expanded)
%              Number of equality atoms :  149 (1552 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_53,axiom,(
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

tff(f_58,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_78,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_87,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_78])).

tff(c_806,plain,(
    ! [A_136,B_137,C_138] :
      ( k1_relset_1(A_136,B_137,C_138) = k1_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_815,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_806])).

tff(c_831,plain,(
    ! [A_143,B_144,C_145] :
      ( m1_subset_1(k1_relset_1(A_143,B_144,C_145),k1_zfmisc_1(A_143))
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_852,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_815,c_831])).

tff(c_859,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_852])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_867,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_859,c_28])).

tff(c_781,plain,(
    ! [A_130,B_131,C_132] :
      ( k2_relset_1(A_130,B_131,C_132) = k2_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_790,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_781])).

tff(c_42,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_791,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_42])).

tff(c_1007,plain,(
    ! [C_179,A_180,B_181] :
      ( m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181)))
      | ~ r1_tarski(k2_relat_1(C_179),B_181)
      | ~ r1_tarski(k1_relat_1(C_179),A_180)
      | ~ v1_relat_1(C_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_106,plain,(
    ! [B_39,A_40] :
      ( v1_xboole_0(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_130,plain,(
    ! [A_44,B_45] :
      ( v1_xboole_0(A_44)
      | ~ v1_xboole_0(B_45)
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_30,c_106])).

tff(c_138,plain,
    ( v1_xboole_0(k2_relset_1('#skF_1','#skF_2','#skF_4'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_130])).

tff(c_139,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_38,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38])).

tff(c_98,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_40,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_51,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_116,plain,(
    ! [A_41,B_42,C_43] :
      ( k1_relset_1(A_41,B_42,C_43) = k1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_125,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_116])).

tff(c_461,plain,(
    ! [B_102,A_103,C_104] :
      ( k1_xboole_0 = B_102
      | k1_relset_1(A_103,B_102,C_104) = A_103
      | ~ v1_funct_2(C_104,A_103,B_102)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_475,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_461])).

tff(c_481,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_125,c_475])).

tff(c_482,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_481])).

tff(c_162,plain,(
    ! [A_54,B_55,C_56] :
      ( m1_subset_1(k1_relset_1(A_54,B_55,C_56),k1_zfmisc_1(A_54))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_183,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_162])).

tff(c_190,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_183])).

tff(c_198,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_190,c_28])).

tff(c_152,plain,(
    ! [A_51,B_52,C_53] :
      ( k2_relset_1(A_51,B_52,C_53) = k2_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_161,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_152])).

tff(c_204,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_42])).

tff(c_341,plain,(
    ! [C_88,A_89,B_90] :
      ( m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ r1_tarski(k2_relat_1(C_88),B_90)
      | ~ r1_tarski(k1_relat_1(C_88),A_89)
      | ~ v1_relat_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_405,plain,(
    ! [C_95,A_96,B_97] :
      ( r1_tarski(C_95,k2_zfmisc_1(A_96,B_97))
      | ~ r1_tarski(k2_relat_1(C_95),B_97)
      | ~ r1_tarski(k1_relat_1(C_95),A_96)
      | ~ v1_relat_1(C_95) ) ),
    inference(resolution,[status(thm)],[c_341,c_28])).

tff(c_407,plain,(
    ! [A_96] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_96,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_96)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_204,c_405])).

tff(c_411,plain,(
    ! [A_98] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_98,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_407])).

tff(c_415,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_198,c_411])).

tff(c_124,plain,(
    ! [A_41,B_42,A_22] :
      ( k1_relset_1(A_41,B_42,A_22) = k1_relat_1(A_22)
      | ~ r1_tarski(A_22,k2_zfmisc_1(A_41,B_42)) ) ),
    inference(resolution,[status(thm)],[c_30,c_116])).

tff(c_433,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_415,c_124])).

tff(c_483,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_433])).

tff(c_580,plain,(
    ! [B_107,C_108,A_109] :
      ( k1_xboole_0 = B_107
      | v1_funct_2(C_108,A_109,B_107)
      | k1_relset_1(A_109,B_107,C_108) != A_109
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_630,plain,(
    ! [B_114,A_115,A_116] :
      ( k1_xboole_0 = B_114
      | v1_funct_2(A_115,A_116,B_114)
      | k1_relset_1(A_116,B_114,A_115) != A_116
      | ~ r1_tarski(A_115,k2_zfmisc_1(A_116,B_114)) ) ),
    inference(resolution,[status(thm)],[c_30,c_580])).

tff(c_636,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_415,c_630])).

tff(c_647,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_636])).

tff(c_648,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_647])).

tff(c_20,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_52,plain,(
    ! [A_26] :
      ( k1_xboole_0 = A_26
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_56,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_52])).

tff(c_57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_20])).

tff(c_671,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_57])).

tff(c_676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_671])).

tff(c_678,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_36,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_682,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_678,c_36])).

tff(c_34,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) = k1_xboole_0
      | k1_relat_1(A_24) != k1_xboole_0
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_95,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_87,c_34])).

tff(c_97,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_32,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) = k1_xboole_0
      | k2_relat_1(A_24) != k1_xboole_0
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_96,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_87,c_32])).

tff(c_99,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_96])).

tff(c_683,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_99])).

tff(c_677,plain,(
    v1_xboole_0(k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_689,plain,(
    ! [A_25] :
      ( A_25 = '#skF_3'
      | ~ v1_xboole_0(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_36])).

tff(c_709,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_677,c_689])).

tff(c_735,plain,(
    ! [A_120,B_121,C_122] :
      ( k2_relset_1(A_120,B_121,C_122) = k2_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_742,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_735])).

tff(c_745,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_709,c_742])).

tff(c_747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_683,c_745])).

tff(c_748,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1044,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1007,c_748])).

tff(c_1064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_867,c_791,c_1044])).

tff(c_1066,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_2161,plain,(
    ! [A_308,B_309,C_310] :
      ( k1_relset_1(A_308,B_309,C_310) = k1_relat_1(C_310)
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(A_308,B_309))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2168,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_2161])).

tff(c_2171,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_2168])).

tff(c_2182,plain,(
    ! [A_314,B_315,C_316] :
      ( m1_subset_1(k1_relset_1(A_314,B_315,C_316),k1_zfmisc_1(A_314))
      | ~ m1_subset_1(C_316,k1_zfmisc_1(k2_zfmisc_1(A_314,B_315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2203,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2171,c_2182])).

tff(c_2210,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2203])).

tff(c_2230,plain,(
    r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_2210,c_28])).

tff(c_1065,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_2128,plain,(
    ! [A_300,B_301,C_302] :
      ( k2_relset_1(A_300,B_301,C_302) = k2_relat_1(C_302)
      | ~ m1_subset_1(C_302,k1_zfmisc_1(k2_zfmisc_1(A_300,B_301))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2135,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_2128])).

tff(c_2138,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1065,c_2135])).

tff(c_2139,plain,(
    r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2138,c_42])).

tff(c_2358,plain,(
    ! [C_349,A_350,B_351] :
      ( m1_subset_1(C_349,k1_zfmisc_1(k2_zfmisc_1(A_350,B_351)))
      | ~ r1_tarski(k2_relat_1(C_349),B_351)
      | ~ r1_tarski(k1_relat_1(C_349),A_350)
      | ~ v1_relat_1(C_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1131,plain,(
    ! [A_195,B_196,C_197] :
      ( k1_relset_1(A_195,B_196,C_197) = k1_relat_1(C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1138,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1131])).

tff(c_1141,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_1138])).

tff(c_1507,plain,(
    ! [B_250,A_251,C_252] :
      ( k1_xboole_0 = B_250
      | k1_relset_1(A_251,B_250,C_252) = A_251
      | ~ v1_funct_2(C_252,A_251,B_250)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_251,B_250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1521,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1507])).

tff(c_1527,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1141,c_1521])).

tff(c_1528,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_1527])).

tff(c_1104,plain,(
    ! [A_189,B_190,C_191] :
      ( k2_relset_1(A_189,B_190,C_191) = k2_relat_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1111,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1104])).

tff(c_1114,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1065,c_1111])).

tff(c_1115,plain,(
    r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_42])).

tff(c_1549,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_1115])).

tff(c_1157,plain,(
    ! [A_202,B_203,C_204] :
      ( m1_subset_1(k1_relset_1(A_202,B_203,C_204),k1_zfmisc_1(A_202))
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1178,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1141,c_1157])).

tff(c_1185,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1178])).

tff(c_1194,plain,(
    r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_1185,c_28])).

tff(c_1334,plain,(
    ! [C_238,A_239,B_240] :
      ( m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240)))
      | ~ r1_tarski(k2_relat_1(C_238),B_240)
      | ~ r1_tarski(k1_relat_1(C_238),A_239)
      | ~ v1_relat_1(C_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1387,plain,(
    ! [C_241,A_242,B_243] :
      ( r1_tarski(C_241,k2_zfmisc_1(A_242,B_243))
      | ~ r1_tarski(k2_relat_1(C_241),B_243)
      | ~ r1_tarski(k1_relat_1(C_241),A_242)
      | ~ v1_relat_1(C_241) ) ),
    inference(resolution,[status(thm)],[c_1334,c_28])).

tff(c_1389,plain,(
    ! [A_242,B_243] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_242,B_243))
      | ~ r1_tarski(k1_xboole_0,B_243)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_242)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1065,c_1387])).

tff(c_1392,plain,(
    ! [A_244,B_245] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_244,B_245))
      | ~ r1_tarski(k1_xboole_0,B_245)
      | ~ r1_tarski(k1_xboole_0,A_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1066,c_1389])).

tff(c_1139,plain,(
    ! [A_195,B_196,A_22] :
      ( k1_relset_1(A_195,B_196,A_22) = k1_relat_1(A_22)
      | ~ r1_tarski(A_22,k2_zfmisc_1(A_195,B_196)) ) ),
    inference(resolution,[status(thm)],[c_30,c_1131])).

tff(c_1414,plain,(
    ! [A_244,B_245] :
      ( k1_relset_1(A_244,B_245,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_xboole_0,B_245)
      | ~ r1_tarski(k1_xboole_0,A_244) ) ),
    inference(resolution,[status(thm)],[c_1392,c_1139])).

tff(c_1436,plain,(
    ! [A_246,B_247] :
      ( k1_relset_1(A_246,B_247,'#skF_4') = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_247)
      | ~ r1_tarski(k1_xboole_0,A_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_1414])).

tff(c_1443,plain,(
    ! [A_248] :
      ( k1_relset_1(A_248,'#skF_3','#skF_4') = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_248) ) ),
    inference(resolution,[status(thm)],[c_1115,c_1436])).

tff(c_1450,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1194,c_1443])).

tff(c_1534,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_1450])).

tff(c_1545,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_1194])).

tff(c_1391,plain,(
    ! [A_242,B_243] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_242,B_243))
      | ~ r1_tarski(k1_xboole_0,B_243)
      | ~ r1_tarski(k1_xboole_0,A_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1066,c_1389])).

tff(c_1537,plain,(
    ! [A_242,B_243] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_242,B_243))
      | ~ r1_tarski('#skF_1',B_243)
      | ~ r1_tarski('#skF_1',A_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_1528,c_1391])).

tff(c_1283,plain,(
    ! [C_222,B_223] :
      ( v1_funct_2(C_222,k1_xboole_0,B_223)
      | k1_relset_1(k1_xboole_0,B_223,C_222) != k1_xboole_0
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1293,plain,(
    ! [A_22,B_223] :
      ( v1_funct_2(A_22,k1_xboole_0,B_223)
      | k1_relset_1(k1_xboole_0,B_223,A_22) != k1_xboole_0
      | ~ r1_tarski(A_22,k2_zfmisc_1(k1_xboole_0,B_223)) ) ),
    inference(resolution,[status(thm)],[c_30,c_1283])).

tff(c_2051,plain,(
    ! [A_290,B_291] :
      ( v1_funct_2(A_290,'#skF_1',B_291)
      | k1_relset_1('#skF_1',B_291,A_290) != '#skF_1'
      | ~ r1_tarski(A_290,k2_zfmisc_1('#skF_1',B_291)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_1528,c_1528,c_1528,c_1293])).

tff(c_2055,plain,(
    ! [B_243] :
      ( v1_funct_2('#skF_4','#skF_1',B_243)
      | k1_relset_1('#skF_1',B_243,'#skF_4') != '#skF_1'
      | ~ r1_tarski('#skF_1',B_243)
      | ~ r1_tarski('#skF_1','#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1537,c_2051])).

tff(c_2070,plain,(
    ! [B_292] :
      ( v1_funct_2('#skF_4','#skF_1',B_292)
      | k1_relset_1('#skF_1',B_292,'#skF_4') != '#skF_1'
      | ~ r1_tarski('#skF_1',B_292) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1545,c_2055])).

tff(c_1067,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_2077,plain,
    ( k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_2070,c_1067])).

tff(c_2085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1549,c_1534,c_2077])).

tff(c_2086,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2395,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2358,c_2086])).

tff(c_2415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_2230,c_1066,c_2139,c_1065,c_2395])).

tff(c_2416,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2417,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2422,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2416,c_2417])).

tff(c_2444,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_44])).

tff(c_4062,plain,(
    ! [C_514,A_515,B_516] :
      ( v1_relat_1(C_514)
      | ~ m1_subset_1(C_514,k1_zfmisc_1(k2_zfmisc_1(A_515,B_516))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_4071,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2444,c_4062])).

tff(c_4060,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) = '#skF_1'
      | k2_relat_1(A_24) != '#skF_1'
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2416,c_2416,c_32])).

tff(c_4078,plain,
    ( k1_relat_1('#skF_4') = '#skF_1'
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_4071,c_4060])).

tff(c_4080,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4078])).

tff(c_4058,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) = '#skF_1'
      | k1_relat_1(A_24) != '#skF_1'
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2416,c_2416,c_34])).

tff(c_4079,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | k1_relat_1('#skF_4') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_4071,c_4058])).

tff(c_4091,plain,(
    k1_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_4080,c_4079])).

tff(c_2429,plain,(
    ! [A_352] :
      ( A_352 = '#skF_1'
      | ~ v1_xboole_0(A_352) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2416,c_36])).

tff(c_2433,plain,(
    o_0_0_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_2429])).

tff(c_2434,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2433,c_20])).

tff(c_4139,plain,(
    ! [A_531,B_532,C_533] :
      ( k1_relset_1(A_531,B_532,C_533) = k1_relat_1(C_533)
      | ~ m1_subset_1(C_533,k1_zfmisc_1(k2_zfmisc_1(A_531,B_532))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4148,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2444,c_4139])).

tff(c_4160,plain,(
    ! [A_538,B_539,C_540] :
      ( m1_subset_1(k1_relset_1(A_538,B_539,C_540),k1_zfmisc_1(A_538))
      | ~ m1_subset_1(C_540,k1_zfmisc_1(k2_zfmisc_1(A_538,B_539))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4181,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4148,c_4160])).

tff(c_4188,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2444,c_4181])).

tff(c_4,plain,(
    ! [B_6,A_4] :
      ( v1_xboole_0(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_4))
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4191,plain,
    ( v1_xboole_0(k1_relat_1('#skF_4'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4188,c_4])).

tff(c_4197,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2434,c_4191])).

tff(c_2428,plain,(
    ! [A_25] :
      ( A_25 = '#skF_1'
      | ~ v1_xboole_0(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2416,c_36])).

tff(c_4220,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4197,c_2428])).

tff(c_4224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4091,c_4220])).

tff(c_4225,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4078])).

tff(c_4262,plain,(
    ! [A_550,B_551,C_552] :
      ( k1_relset_1(A_550,B_551,C_552) = k1_relat_1(C_552)
      | ~ m1_subset_1(C_552,k1_zfmisc_1(k2_zfmisc_1(A_550,B_551))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4269,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2444,c_4262])).

tff(c_4272,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4225,c_4269])).

tff(c_4312,plain,(
    ! [A_561,B_562,C_563] :
      ( m1_subset_1(k1_relset_1(A_561,B_562,C_563),k1_zfmisc_1(A_561))
      | ~ m1_subset_1(C_563,k1_zfmisc_1(k2_zfmisc_1(A_561,B_562))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4333,plain,
    ( m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4272,c_4312])).

tff(c_4340,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2444,c_4333])).

tff(c_4350,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_4340,c_28])).

tff(c_4226,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4078])).

tff(c_4291,plain,(
    ! [A_558,B_559,C_560] :
      ( k2_relset_1(A_558,B_559,C_560) = k2_relat_1(C_560)
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(A_558,B_559))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4298,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2444,c_4291])).

tff(c_4301,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4226,c_4298])).

tff(c_2445,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_1','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_42])).

tff(c_4302,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4301,c_2445])).

tff(c_4516,plain,(
    ! [C_593,A_594,B_595] :
      ( m1_subset_1(C_593,k1_zfmisc_1(k2_zfmisc_1(A_594,B_595)))
      | ~ r1_tarski(k2_relat_1(C_593),B_595)
      | ~ r1_tarski(k1_relat_1(C_593),A_594)
      | ~ v1_relat_1(C_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2457,plain,(
    ! [C_357,A_358,B_359] :
      ( v1_relat_1(C_357)
      | ~ m1_subset_1(C_357,k1_zfmisc_1(k2_zfmisc_1(A_358,B_359))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2466,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2444,c_2457])).

tff(c_2468,plain,(
    ! [A_360] :
      ( k2_relat_1(A_360) = '#skF_1'
      | k1_relat_1(A_360) != '#skF_1'
      | ~ v1_relat_1(A_360) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2416,c_2416,c_34])).

tff(c_2472,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | k1_relat_1('#skF_4') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_2466,c_2468])).

tff(c_2473,plain,(
    k1_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2472])).

tff(c_2535,plain,(
    ! [A_375,B_376,C_377] :
      ( k1_relset_1(A_375,B_376,C_377) = k1_relat_1(C_377)
      | ~ m1_subset_1(C_377,k1_zfmisc_1(k2_zfmisc_1(A_375,B_376))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2544,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2444,c_2535])).

tff(c_2562,plain,(
    ! [A_383,B_384,C_385] :
      ( m1_subset_1(k1_relset_1(A_383,B_384,C_385),k1_zfmisc_1(A_383))
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(A_383,B_384))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2583,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2544,c_2562])).

tff(c_2590,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2444,c_2583])).

tff(c_2593,plain,
    ( v1_xboole_0(k1_relat_1('#skF_4'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2590,c_4])).

tff(c_2599,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2434,c_2593])).

tff(c_2603,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2599,c_2428])).

tff(c_2607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2473,c_2603])).

tff(c_2608,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2472])).

tff(c_2679,plain,(
    ! [A_401,B_402,C_403] :
      ( k2_relset_1(A_401,B_402,C_403) = k2_relat_1(C_403)
      | ~ m1_subset_1(C_403,k1_zfmisc_1(k2_zfmisc_1(A_401,B_402))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2686,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2444,c_2679])).

tff(c_2689,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2608,c_2686])).

tff(c_2690,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2689,c_2445])).

tff(c_2609,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2472])).

tff(c_2652,plain,(
    ! [A_394,B_395,C_396] :
      ( k1_relset_1(A_394,B_395,C_396) = k1_relat_1(C_396)
      | ~ m1_subset_1(C_396,k1_zfmisc_1(k2_zfmisc_1(A_394,B_395))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2659,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2444,c_2652])).

tff(c_2662,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2609,c_2659])).

tff(c_2701,plain,(
    ! [A_405,B_406,C_407] :
      ( m1_subset_1(k1_relset_1(A_405,B_406,C_407),k1_zfmisc_1(A_405))
      | ~ m1_subset_1(C_407,k1_zfmisc_1(k2_zfmisc_1(A_405,B_406))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2722,plain,
    ( m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2662,c_2701])).

tff(c_2729,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2444,c_2722])).

tff(c_2739,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2729,c_28])).

tff(c_2928,plain,(
    ! [C_443,A_444,B_445] :
      ( m1_subset_1(C_443,k1_zfmisc_1(k2_zfmisc_1(A_444,B_445)))
      | ~ r1_tarski(k2_relat_1(C_443),B_445)
      | ~ r1_tarski(k1_relat_1(C_443),A_444)
      | ~ v1_relat_1(C_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2981,plain,(
    ! [C_446,A_447,B_448] :
      ( r1_tarski(C_446,k2_zfmisc_1(A_447,B_448))
      | ~ r1_tarski(k2_relat_1(C_446),B_448)
      | ~ r1_tarski(k1_relat_1(C_446),A_447)
      | ~ v1_relat_1(C_446) ) ),
    inference(resolution,[status(thm)],[c_2928,c_28])).

tff(c_2983,plain,(
    ! [A_447,B_448] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_447,B_448))
      | ~ r1_tarski('#skF_1',B_448)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_447)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2608,c_2981])).

tff(c_2986,plain,(
    ! [A_449,B_450] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_449,B_450))
      | ~ r1_tarski('#skF_1',B_450)
      | ~ r1_tarski('#skF_1',A_449) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2466,c_2609,c_2983])).

tff(c_2660,plain,(
    ! [A_394,B_395,A_22] :
      ( k1_relset_1(A_394,B_395,A_22) = k1_relat_1(A_22)
      | ~ r1_tarski(A_22,k2_zfmisc_1(A_394,B_395)) ) ),
    inference(resolution,[status(thm)],[c_30,c_2652])).

tff(c_3011,plain,(
    ! [A_449,B_450] :
      ( k1_relset_1(A_449,B_450,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',B_450)
      | ~ r1_tarski('#skF_1',A_449) ) ),
    inference(resolution,[status(thm)],[c_2986,c_2660])).

tff(c_3862,plain,(
    ! [A_502,B_503] :
      ( k1_relset_1(A_502,B_503,'#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',B_503)
      | ~ r1_tarski('#skF_1',A_502) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2609,c_3011])).

tff(c_3869,plain,(
    ! [A_504] :
      ( k1_relset_1(A_504,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_504) ) ),
    inference(resolution,[status(thm)],[c_2690,c_3862])).

tff(c_3876,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2739,c_3869])).

tff(c_10,plain,(
    ! [C_9,B_8] :
      ( v1_funct_2(C_9,k1_xboole_0,B_8)
      | k1_relset_1(k1_xboole_0,B_8,C_9) != k1_xboole_0
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2852,plain,(
    ! [C_427,B_428] :
      ( v1_funct_2(C_427,'#skF_1',B_428)
      | k1_relset_1('#skF_1',B_428,C_427) != '#skF_1'
      | ~ m1_subset_1(C_427,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_428))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2416,c_2416,c_2416,c_2416,c_10])).

tff(c_2865,plain,(
    ! [A_22,B_428] :
      ( v1_funct_2(A_22,'#skF_1',B_428)
      | k1_relset_1('#skF_1',B_428,A_22) != '#skF_1'
      | ~ r1_tarski(A_22,k2_zfmisc_1('#skF_1',B_428)) ) ),
    inference(resolution,[status(thm)],[c_30,c_2852])).

tff(c_2998,plain,(
    ! [B_450] :
      ( v1_funct_2('#skF_4','#skF_1',B_450)
      | k1_relset_1('#skF_1',B_450,'#skF_4') != '#skF_1'
      | ~ r1_tarski('#skF_1',B_450)
      | ~ r1_tarski('#skF_1','#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2986,c_2865])).

tff(c_4031,plain,(
    ! [B_509] :
      ( v1_funct_2('#skF_4','#skF_1',B_509)
      | k1_relset_1('#skF_1',B_509,'#skF_4') != '#skF_1'
      | ~ r1_tarski('#skF_1',B_509) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2739,c_2998])).

tff(c_2451,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_4038,plain,
    ( k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_4031,c_2451])).

tff(c_4046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2690,c_3876,c_4038])).

tff(c_4047,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_4552,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4516,c_4047])).

tff(c_4569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4071,c_4350,c_4225,c_4302,c_4226,c_4552])).

%------------------------------------------------------------------------------
