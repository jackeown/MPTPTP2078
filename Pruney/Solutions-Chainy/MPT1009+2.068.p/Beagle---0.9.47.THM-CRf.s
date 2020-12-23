%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:51 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 211 expanded)
%              Number of leaves         :   41 (  88 expanded)
%              Depth                    :   13
%              Number of atoms          :  114 ( 391 expanded)
%              Number of equality atoms :   47 ( 135 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_64,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_85,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_93,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_85])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k9_relat_1(B_15,A_14),k2_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) != k1_xboole_0
      | k1_xboole_0 = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_101,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_93,c_30])).

tff(c_122,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_145,plain,(
    ! [C_53,A_54,B_55] :
      ( v4_relat_1(C_53,A_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_153,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_145])).

tff(c_157,plain,(
    ! [B_58,A_59] :
      ( k7_relat_1(B_58,A_59) = B_58
      | ~ v4_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_160,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_153,c_157])).

tff(c_166,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_160])).

tff(c_273,plain,(
    ! [B_80,A_81] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_80,k1_tarski(A_81))),k1_tarski(k1_funct_1(B_80,A_81)))
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_283,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),k1_tarski(k1_funct_1('#skF_4','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_273])).

tff(c_290,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_52,c_283])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k1_tarski(B_9) = A_8
      | k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_tarski(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_295,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4')
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_290,c_10])).

tff(c_298,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_295])).

tff(c_247,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( k7_relset_1(A_72,B_73,C_74,D_75) = k9_relat_1(C_74,D_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_253,plain,(
    ! [D_75] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_75) = k9_relat_1('#skF_4',D_75) ),
    inference(resolution,[status(thm)],[c_48,c_247])).

tff(c_44,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_263,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_44])).

tff(c_300,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_263])).

tff(c_328,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_300])).

tff(c_332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_328])).

tff(c_333,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_342,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_333,c_28])).

tff(c_32,plain,(
    ! [A_20] :
      ( k1_relat_1(A_20) != k1_xboole_0
      | k1_xboole_0 = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_102,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_93,c_32])).

tff(c_121,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_335,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_121])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_335])).

tff(c_380,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_386,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_2])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_387,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_380,c_26])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_385,plain,(
    ! [A_10] : m1_subset_1('#skF_4',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_16])).

tff(c_462,plain,(
    ! [C_95,A_96,B_97] :
      ( v4_relat_1(C_95,A_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_467,plain,(
    ! [A_96] : v4_relat_1('#skF_4',A_96) ),
    inference(resolution,[status(thm)],[c_385,c_462])).

tff(c_469,plain,(
    ! [B_99,A_100] :
      ( k7_relat_1(B_99,A_100) = B_99
      | ~ v4_relat_1(B_99,A_100)
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_472,plain,(
    ! [A_96] :
      ( k7_relat_1('#skF_4',A_96) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_467,c_469])).

tff(c_475,plain,(
    ! [A_96] : k7_relat_1('#skF_4',A_96) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_472])).

tff(c_490,plain,(
    ! [B_106,A_107] :
      ( k2_relat_1(k7_relat_1(B_106,A_107)) = k9_relat_1(B_106,A_107)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_502,plain,(
    ! [A_96] :
      ( k9_relat_1('#skF_4',A_96) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_490])).

tff(c_506,plain,(
    ! [A_96] : k9_relat_1('#skF_4',A_96) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_387,c_502])).

tff(c_526,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( k7_relset_1(A_114,B_115,C_116,D_117) = k9_relat_1(C_116,D_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_529,plain,(
    ! [A_114,B_115,D_117] : k7_relset_1(A_114,B_115,'#skF_4',D_117) = k9_relat_1('#skF_4',D_117) ),
    inference(resolution,[status(thm)],[c_385,c_526])).

tff(c_531,plain,(
    ! [A_114,B_115,D_117] : k7_relset_1(A_114,B_115,'#skF_4',D_117) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_529])).

tff(c_532,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_44])).

tff(c_535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_532])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:15:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.41  
% 2.54/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.41  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.54/1.41  
% 2.54/1.41  %Foreground sorts:
% 2.54/1.41  
% 2.54/1.41  
% 2.54/1.41  %Background operators:
% 2.54/1.41  
% 2.54/1.41  
% 2.54/1.41  %Foreground operators:
% 2.54/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.54/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.54/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.54/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.54/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.54/1.41  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.54/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.54/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.54/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.54/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.54/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.54/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.54/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.54/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.54/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.41  
% 2.77/1.43  tff(f_104, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.77/1.43  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.77/1.43  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 2.77/1.43  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.77/1.43  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.77/1.43  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.77/1.43  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 2.77/1.43  tff(f_39, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.77/1.43  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.77/1.43  tff(f_64, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.77/1.43  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.77/1.43  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.77/1.43  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.77/1.43  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.77/1.43  tff(c_85, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.77/1.43  tff(c_93, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_85])).
% 2.77/1.43  tff(c_20, plain, (![B_15, A_14]: (r1_tarski(k9_relat_1(B_15, A_14), k2_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.77/1.43  tff(c_30, plain, (![A_20]: (k2_relat_1(A_20)!=k1_xboole_0 | k1_xboole_0=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.77/1.43  tff(c_101, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_93, c_30])).
% 2.77/1.43  tff(c_122, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_101])).
% 2.77/1.43  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.77/1.43  tff(c_145, plain, (![C_53, A_54, B_55]: (v4_relat_1(C_53, A_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.77/1.43  tff(c_153, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_145])).
% 2.77/1.43  tff(c_157, plain, (![B_58, A_59]: (k7_relat_1(B_58, A_59)=B_58 | ~v4_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.77/1.43  tff(c_160, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_153, c_157])).
% 2.77/1.43  tff(c_166, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_160])).
% 2.77/1.43  tff(c_273, plain, (![B_80, A_81]: (r1_tarski(k2_relat_1(k7_relat_1(B_80, k1_tarski(A_81))), k1_tarski(k1_funct_1(B_80, A_81))) | ~v1_funct_1(B_80) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.77/1.43  tff(c_283, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_tarski(k1_funct_1('#skF_4', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_166, c_273])).
% 2.77/1.43  tff(c_290, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_52, c_283])).
% 2.77/1.43  tff(c_10, plain, (![B_9, A_8]: (k1_tarski(B_9)=A_8 | k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_tarski(B_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.43  tff(c_295, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4') | k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_290, c_10])).
% 2.77/1.43  tff(c_298, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_122, c_295])).
% 2.77/1.43  tff(c_247, plain, (![A_72, B_73, C_74, D_75]: (k7_relset_1(A_72, B_73, C_74, D_75)=k9_relat_1(C_74, D_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.77/1.43  tff(c_253, plain, (![D_75]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_75)=k9_relat_1('#skF_4', D_75))), inference(resolution, [status(thm)], [c_48, c_247])).
% 2.77/1.43  tff(c_44, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.77/1.43  tff(c_263, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_44])).
% 2.77/1.43  tff(c_300, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_298, c_263])).
% 2.77/1.43  tff(c_328, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_300])).
% 2.77/1.43  tff(c_332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_328])).
% 2.77/1.43  tff(c_333, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_101])).
% 2.77/1.43  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.77/1.43  tff(c_342, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_333, c_333, c_28])).
% 2.77/1.43  tff(c_32, plain, (![A_20]: (k1_relat_1(A_20)!=k1_xboole_0 | k1_xboole_0=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.77/1.43  tff(c_102, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_93, c_32])).
% 2.77/1.43  tff(c_121, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_102])).
% 2.77/1.43  tff(c_335, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_333, c_121])).
% 2.77/1.43  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_342, c_335])).
% 2.77/1.43  tff(c_380, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_102])).
% 2.77/1.43  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.77/1.43  tff(c_386, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_380, c_2])).
% 2.77/1.43  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.77/1.43  tff(c_387, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_380, c_380, c_26])).
% 2.77/1.43  tff(c_16, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.77/1.43  tff(c_385, plain, (![A_10]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_380, c_16])).
% 2.77/1.43  tff(c_462, plain, (![C_95, A_96, B_97]: (v4_relat_1(C_95, A_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.77/1.43  tff(c_467, plain, (![A_96]: (v4_relat_1('#skF_4', A_96))), inference(resolution, [status(thm)], [c_385, c_462])).
% 2.77/1.43  tff(c_469, plain, (![B_99, A_100]: (k7_relat_1(B_99, A_100)=B_99 | ~v4_relat_1(B_99, A_100) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.77/1.43  tff(c_472, plain, (![A_96]: (k7_relat_1('#skF_4', A_96)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_467, c_469])).
% 2.77/1.43  tff(c_475, plain, (![A_96]: (k7_relat_1('#skF_4', A_96)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_472])).
% 2.77/1.43  tff(c_490, plain, (![B_106, A_107]: (k2_relat_1(k7_relat_1(B_106, A_107))=k9_relat_1(B_106, A_107) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.77/1.43  tff(c_502, plain, (![A_96]: (k9_relat_1('#skF_4', A_96)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_475, c_490])).
% 2.77/1.43  tff(c_506, plain, (![A_96]: (k9_relat_1('#skF_4', A_96)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_387, c_502])).
% 2.77/1.43  tff(c_526, plain, (![A_114, B_115, C_116, D_117]: (k7_relset_1(A_114, B_115, C_116, D_117)=k9_relat_1(C_116, D_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.77/1.43  tff(c_529, plain, (![A_114, B_115, D_117]: (k7_relset_1(A_114, B_115, '#skF_4', D_117)=k9_relat_1('#skF_4', D_117))), inference(resolution, [status(thm)], [c_385, c_526])).
% 2.77/1.43  tff(c_531, plain, (![A_114, B_115, D_117]: (k7_relset_1(A_114, B_115, '#skF_4', D_117)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_506, c_529])).
% 2.77/1.43  tff(c_532, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_531, c_44])).
% 2.77/1.43  tff(c_535, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_386, c_532])).
% 2.77/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.43  
% 2.77/1.43  Inference rules
% 2.77/1.43  ----------------------
% 2.77/1.43  #Ref     : 0
% 2.77/1.43  #Sup     : 98
% 2.77/1.43  #Fact    : 0
% 2.77/1.43  #Define  : 0
% 2.77/1.43  #Split   : 2
% 2.77/1.43  #Chain   : 0
% 2.77/1.43  #Close   : 0
% 2.77/1.43  
% 2.77/1.43  Ordering : KBO
% 2.77/1.43  
% 2.77/1.43  Simplification rules
% 2.77/1.43  ----------------------
% 2.77/1.43  #Subsume      : 0
% 2.77/1.43  #Demod        : 93
% 2.77/1.43  #Tautology    : 74
% 2.77/1.43  #SimpNegUnit  : 1
% 2.77/1.43  #BackRed      : 23
% 2.77/1.43  
% 2.77/1.43  #Partial instantiations: 0
% 2.77/1.43  #Strategies tried      : 1
% 2.77/1.43  
% 2.77/1.43  Timing (in seconds)
% 2.77/1.43  ----------------------
% 2.77/1.43  Preprocessing        : 0.34
% 2.77/1.43  Parsing              : 0.19
% 2.77/1.43  CNF conversion       : 0.02
% 2.77/1.43  Main loop            : 0.25
% 2.77/1.43  Inferencing          : 0.09
% 2.77/1.43  Reduction            : 0.09
% 2.77/1.43  Demodulation         : 0.06
% 2.77/1.43  BG Simplification    : 0.02
% 2.77/1.44  Subsumption          : 0.04
% 2.77/1.44  Abstraction          : 0.01
% 2.77/1.44  MUC search           : 0.00
% 2.77/1.44  Cooper               : 0.00
% 2.77/1.44  Total                : 0.63
% 2.77/1.44  Index Insertion      : 0.00
% 2.77/1.44  Index Deletion       : 0.00
% 2.77/1.44  Index Matching       : 0.00
% 2.77/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
