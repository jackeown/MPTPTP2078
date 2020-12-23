%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:39 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 103 expanded)
%              Number of leaves         :   44 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 166 expanded)
%              Number of equality atoms :   42 (  67 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_128,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_relset_1(A_81,B_82,C_83) = k2_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_132,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_128])).

tff(c_58,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_133,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_58])).

tff(c_32,plain,(
    ! [A_40,B_41] : v1_relat_1(k2_zfmisc_1(A_40,B_41)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_93,plain,(
    ! [B_68,A_69] :
      ( v1_relat_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_96,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_93])).

tff(c_99,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_96])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_171,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( k7_relset_1(A_101,B_102,C_103,D_104) = k9_relat_1(C_103,D_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_174,plain,(
    ! [D_104] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5',D_104) = k9_relat_1('#skF_5',D_104) ),
    inference(resolution,[status(thm)],[c_62,c_171])).

tff(c_226,plain,(
    ! [A_119,B_120,C_121] :
      ( k7_relset_1(A_119,B_120,C_121,A_119) = k2_relset_1(A_119,B_120,C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_228,plain,(
    k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5',k1_tarski('#skF_3')) = k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_226])).

tff(c_230,plain,(
    k9_relat_1('#skF_5',k1_tarski('#skF_3')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_132,c_228])).

tff(c_30,plain,(
    ! [A_37,B_39] :
      ( k9_relat_1(A_37,k1_tarski(B_39)) = k11_relat_1(A_37,B_39)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_245,plain,
    ( k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_30])).

tff(c_252,plain,(
    k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_245])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_64,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_145,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_relset_1(A_87,B_88,C_89) = k1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_149,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_145])).

tff(c_263,plain,(
    ! [B_128,A_129,C_130] :
      ( k1_xboole_0 = B_128
      | k1_relset_1(A_129,B_128,C_130) = A_129
      | ~ v1_funct_2(C_130,A_129,B_128)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_266,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_263])).

tff(c_269,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_149,c_266])).

tff(c_270,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_269])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_296,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_4])).

tff(c_34,plain,(
    ! [B_43,A_42] :
      ( k1_tarski(k1_funct_1(B_43,A_42)) = k11_relat_1(B_43,A_42)
      | ~ r2_hidden(A_42,k1_relat_1(B_43))
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_305,plain,
    ( k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k11_relat_1('#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_296,c_34])).

tff(c_308,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_66,c_252,c_305])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.41  
% 2.62/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.42  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.62/1.42  
% 2.62/1.42  %Foreground sorts:
% 2.62/1.42  
% 2.62/1.42  
% 2.62/1.42  %Background operators:
% 2.62/1.42  
% 2.62/1.42  
% 2.62/1.42  %Foreground operators:
% 2.62/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.62/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.62/1.42  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.62/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.62/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.62/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.42  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.62/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.62/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.62/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.62/1.42  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.62/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.62/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.62/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.62/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.62/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.62/1.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.62/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.62/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.62/1.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.62/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.62/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.42  
% 2.62/1.43  tff(f_116, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 2.62/1.43  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.62/1.43  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.62/1.43  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.62/1.43  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.62/1.43  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.62/1.43  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.62/1.43  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.62/1.43  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.62/1.43  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.62/1.43  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 2.62/1.43  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.62/1.43  tff(c_128, plain, (![A_81, B_82, C_83]: (k2_relset_1(A_81, B_82, C_83)=k2_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.62/1.43  tff(c_132, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_128])).
% 2.62/1.43  tff(c_58, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.62/1.43  tff(c_133, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_58])).
% 2.62/1.43  tff(c_32, plain, (![A_40, B_41]: (v1_relat_1(k2_zfmisc_1(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.62/1.43  tff(c_93, plain, (![B_68, A_69]: (v1_relat_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.62/1.43  tff(c_96, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_93])).
% 2.62/1.43  tff(c_99, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_96])).
% 2.62/1.43  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.62/1.43  tff(c_171, plain, (![A_101, B_102, C_103, D_104]: (k7_relset_1(A_101, B_102, C_103, D_104)=k9_relat_1(C_103, D_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.62/1.43  tff(c_174, plain, (![D_104]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5', D_104)=k9_relat_1('#skF_5', D_104))), inference(resolution, [status(thm)], [c_62, c_171])).
% 2.62/1.43  tff(c_226, plain, (![A_119, B_120, C_121]: (k7_relset_1(A_119, B_120, C_121, A_119)=k2_relset_1(A_119, B_120, C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.62/1.43  tff(c_228, plain, (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5', k1_tarski('#skF_3'))=k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_226])).
% 2.62/1.43  tff(c_230, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_3'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_132, c_228])).
% 2.62/1.43  tff(c_30, plain, (![A_37, B_39]: (k9_relat_1(A_37, k1_tarski(B_39))=k11_relat_1(A_37, B_39) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.62/1.43  tff(c_245, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_230, c_30])).
% 2.62/1.43  tff(c_252, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_245])).
% 2.62/1.43  tff(c_60, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.62/1.43  tff(c_64, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.62/1.43  tff(c_145, plain, (![A_87, B_88, C_89]: (k1_relset_1(A_87, B_88, C_89)=k1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.62/1.43  tff(c_149, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_145])).
% 2.62/1.43  tff(c_263, plain, (![B_128, A_129, C_130]: (k1_xboole_0=B_128 | k1_relset_1(A_129, B_128, C_130)=A_129 | ~v1_funct_2(C_130, A_129, B_128) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_129, B_128))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.62/1.43  tff(c_266, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_62, c_263])).
% 2.62/1.43  tff(c_269, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_149, c_266])).
% 2.62/1.43  tff(c_270, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_269])).
% 2.62/1.43  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.62/1.43  tff(c_296, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_270, c_4])).
% 2.62/1.43  tff(c_34, plain, (![B_43, A_42]: (k1_tarski(k1_funct_1(B_43, A_42))=k11_relat_1(B_43, A_42) | ~r2_hidden(A_42, k1_relat_1(B_43)) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.62/1.43  tff(c_305, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k11_relat_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_296, c_34])).
% 2.62/1.43  tff(c_308, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_66, c_252, c_305])).
% 2.62/1.43  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_308])).
% 2.62/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.43  
% 2.62/1.43  Inference rules
% 2.62/1.43  ----------------------
% 2.62/1.43  #Ref     : 0
% 2.62/1.43  #Sup     : 54
% 2.62/1.43  #Fact    : 0
% 2.62/1.43  #Define  : 0
% 2.62/1.43  #Split   : 0
% 2.62/1.43  #Chain   : 0
% 2.62/1.43  #Close   : 0
% 2.62/1.43  
% 2.62/1.43  Ordering : KBO
% 2.62/1.43  
% 2.62/1.43  Simplification rules
% 2.62/1.43  ----------------------
% 2.62/1.43  #Subsume      : 0
% 2.62/1.43  #Demod        : 30
% 2.62/1.43  #Tautology    : 35
% 2.62/1.43  #SimpNegUnit  : 2
% 2.62/1.43  #BackRed      : 8
% 2.62/1.43  
% 2.62/1.43  #Partial instantiations: 0
% 2.62/1.43  #Strategies tried      : 1
% 2.62/1.43  
% 2.62/1.43  Timing (in seconds)
% 2.62/1.43  ----------------------
% 2.62/1.43  Preprocessing        : 0.38
% 2.62/1.43  Parsing              : 0.20
% 2.62/1.43  CNF conversion       : 0.03
% 2.62/1.43  Main loop            : 0.22
% 2.62/1.43  Inferencing          : 0.08
% 2.62/1.43  Reduction            : 0.07
% 2.62/1.43  Demodulation         : 0.05
% 2.62/1.43  BG Simplification    : 0.02
% 2.62/1.43  Subsumption          : 0.04
% 2.62/1.43  Abstraction          : 0.01
% 2.62/1.43  MUC search           : 0.00
% 2.62/1.43  Cooper               : 0.00
% 2.62/1.43  Total                : 0.63
% 2.62/1.43  Index Insertion      : 0.00
% 2.62/1.43  Index Deletion       : 0.00
% 2.62/1.43  Index Matching       : 0.00
% 2.62/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
