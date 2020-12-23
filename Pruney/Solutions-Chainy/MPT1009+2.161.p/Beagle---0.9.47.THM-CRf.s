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
% DateTime   : Thu Dec  3 10:15:04 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 252 expanded)
%              Number of leaves         :   37 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          :  112 ( 567 expanded)
%              Number of equality atoms :   49 ( 146 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_86,axiom,(
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

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).

tff(c_8,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_68,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_71,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_68])).

tff(c_74,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_71])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_95,plain,(
    ! [B_48,A_49] :
      ( k1_tarski(k1_funct_1(B_48,A_49)) = k2_relat_1(B_48)
      | k1_tarski(A_49) != k1_relat_1(B_48)
      | ~ v1_funct_1(B_48)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_101,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_40])).

tff(c_107,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_48,c_101])).

tff(c_109,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_46,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_85,plain,(
    ! [A_44,B_45,C_46] :
      ( k1_relset_1(A_44,B_45,C_46) = k1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_89,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_85])).

tff(c_139,plain,(
    ! [B_64,A_65,C_66] :
      ( k1_xboole_0 = B_64
      | k1_relset_1(A_65,B_64,C_66) = A_65
      | ~ v1_funct_2(C_66,A_65,B_64)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_142,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_139])).

tff(c_145,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_89,c_142])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_42,c_145])).

tff(c_149,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_154,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_46])).

tff(c_153,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_44])).

tff(c_258,plain,(
    ! [B_92,A_93,C_94] :
      ( k1_xboole_0 = B_92
      | k8_relset_1(A_93,B_92,C_94,B_92) = A_93
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92)))
      | ~ v1_funct_2(C_94,A_93,B_92)
      | ~ v1_funct_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_260,plain,
    ( k1_xboole_0 = '#skF_2'
    | k8_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_153,c_258])).

tff(c_263,plain,
    ( k1_xboole_0 = '#skF_2'
    | k8_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_2') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_154,c_260])).

tff(c_264,plain,(
    k8_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_2') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_263])).

tff(c_76,plain,(
    ! [A_41,B_42,C_43] :
      ( k2_relset_1(A_41,B_42,C_43) = k2_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_80,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_76])).

tff(c_151,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_80])).

tff(c_224,plain,(
    ! [B_86,A_87,C_88] :
      ( k7_relset_1(B_86,A_87,C_88,k8_relset_1(B_86,A_87,C_88,A_87)) = k2_relset_1(B_86,A_87,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(B_86,A_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_226,plain,(
    k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',k8_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_2')) = k2_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_153,c_224])).

tff(c_228,plain,(
    k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',k8_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_2')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_226])).

tff(c_184,plain,(
    ! [A_67,B_68,C_69,D_70] :
      ( k7_relset_1(A_67,B_68,C_69,D_70) = k9_relat_1(C_69,D_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_187,plain,(
    ! [D_70] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_70) = k9_relat_1('#skF_4',D_70) ),
    inference(resolution,[status(thm)],[c_153,c_184])).

tff(c_232,plain,(
    k9_relat_1('#skF_4',k8_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_2')) = k2_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_187])).

tff(c_265,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_232])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k9_relat_1(B_10,A_9),k9_relat_1(B_10,k1_relat_1(B_10)))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_279,plain,(
    ! [A_9] :
      ( r1_tarski(k9_relat_1('#skF_4',A_9),k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_10])).

tff(c_285,plain,(
    ! [A_9] : r1_tarski(k9_relat_1('#skF_4',A_9),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_279])).

tff(c_148,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_183,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_148])).

tff(c_188,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_183])).

tff(c_302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:41:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.33  
% 2.46/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.33  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.46/1.33  
% 2.46/1.33  %Foreground sorts:
% 2.46/1.33  
% 2.46/1.33  
% 2.46/1.33  %Background operators:
% 2.46/1.33  
% 2.46/1.33  
% 2.46/1.33  %Foreground operators:
% 2.46/1.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.46/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.46/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.46/1.33  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.46/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.46/1.33  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.46/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.46/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.46/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.46/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.46/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.46/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.46/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.46/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.46/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.46/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.33  
% 2.46/1.35  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.46/1.35  tff(f_110, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 2.46/1.35  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.46/1.35  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.46/1.35  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.46/1.35  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.46/1.35  tff(f_98, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 2.46/1.35  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.46/1.35  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 2.46/1.35  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.46/1.35  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_relat_1)).
% 2.46/1.35  tff(c_8, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.46/1.35  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.46/1.35  tff(c_68, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.46/1.35  tff(c_71, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_68])).
% 2.46/1.35  tff(c_74, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_71])).
% 2.46/1.35  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.46/1.35  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.46/1.35  tff(c_95, plain, (![B_48, A_49]: (k1_tarski(k1_funct_1(B_48, A_49))=k2_relat_1(B_48) | k1_tarski(A_49)!=k1_relat_1(B_48) | ~v1_funct_1(B_48) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.46/1.35  tff(c_40, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.46/1.35  tff(c_101, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_95, c_40])).
% 2.46/1.35  tff(c_107, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_48, c_101])).
% 2.46/1.35  tff(c_109, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_107])).
% 2.46/1.35  tff(c_46, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.46/1.35  tff(c_85, plain, (![A_44, B_45, C_46]: (k1_relset_1(A_44, B_45, C_46)=k1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.46/1.35  tff(c_89, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_85])).
% 2.46/1.35  tff(c_139, plain, (![B_64, A_65, C_66]: (k1_xboole_0=B_64 | k1_relset_1(A_65, B_64, C_66)=A_65 | ~v1_funct_2(C_66, A_65, B_64) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.46/1.35  tff(c_142, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_44, c_139])).
% 2.46/1.35  tff(c_145, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_89, c_142])).
% 2.46/1.35  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_42, c_145])).
% 2.46/1.35  tff(c_149, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_107])).
% 2.46/1.35  tff(c_154, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_46])).
% 2.46/1.35  tff(c_153, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_44])).
% 2.46/1.35  tff(c_258, plain, (![B_92, A_93, C_94]: (k1_xboole_0=B_92 | k8_relset_1(A_93, B_92, C_94, B_92)=A_93 | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))) | ~v1_funct_2(C_94, A_93, B_92) | ~v1_funct_1(C_94))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.46/1.35  tff(c_260, plain, (k1_xboole_0='#skF_2' | k8_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_2')=k1_relat_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_153, c_258])).
% 2.46/1.35  tff(c_263, plain, (k1_xboole_0='#skF_2' | k8_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_2')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_154, c_260])).
% 2.46/1.35  tff(c_264, plain, (k8_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_2')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_263])).
% 2.46/1.35  tff(c_76, plain, (![A_41, B_42, C_43]: (k2_relset_1(A_41, B_42, C_43)=k2_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.46/1.35  tff(c_80, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_76])).
% 2.46/1.35  tff(c_151, plain, (k2_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_80])).
% 2.46/1.35  tff(c_224, plain, (![B_86, A_87, C_88]: (k7_relset_1(B_86, A_87, C_88, k8_relset_1(B_86, A_87, C_88, A_87))=k2_relset_1(B_86, A_87, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(B_86, A_87))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.46/1.35  tff(c_226, plain, (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', k8_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_2'))=k2_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_153, c_224])).
% 2.46/1.35  tff(c_228, plain, (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', k8_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_2'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_226])).
% 2.46/1.35  tff(c_184, plain, (![A_67, B_68, C_69, D_70]: (k7_relset_1(A_67, B_68, C_69, D_70)=k9_relat_1(C_69, D_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.46/1.35  tff(c_187, plain, (![D_70]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_70)=k9_relat_1('#skF_4', D_70))), inference(resolution, [status(thm)], [c_153, c_184])).
% 2.46/1.35  tff(c_232, plain, (k9_relat_1('#skF_4', k8_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_2'))=k2_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_228, c_187])).
% 2.46/1.35  tff(c_265, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_232])).
% 2.46/1.35  tff(c_10, plain, (![B_10, A_9]: (r1_tarski(k9_relat_1(B_10, A_9), k9_relat_1(B_10, k1_relat_1(B_10))) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.46/1.35  tff(c_279, plain, (![A_9]: (r1_tarski(k9_relat_1('#skF_4', A_9), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_265, c_10])).
% 2.46/1.35  tff(c_285, plain, (![A_9]: (r1_tarski(k9_relat_1('#skF_4', A_9), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_279])).
% 2.46/1.35  tff(c_148, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_107])).
% 2.46/1.35  tff(c_183, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_148])).
% 2.46/1.35  tff(c_188, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_183])).
% 2.46/1.35  tff(c_302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_285, c_188])).
% 2.46/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.35  
% 2.46/1.35  Inference rules
% 2.46/1.35  ----------------------
% 2.46/1.35  #Ref     : 0
% 2.46/1.35  #Sup     : 57
% 2.46/1.35  #Fact    : 0
% 2.46/1.35  #Define  : 0
% 2.46/1.35  #Split   : 1
% 2.46/1.35  #Chain   : 0
% 2.46/1.35  #Close   : 0
% 2.46/1.35  
% 2.46/1.35  Ordering : KBO
% 2.46/1.35  
% 2.46/1.35  Simplification rules
% 2.46/1.35  ----------------------
% 2.46/1.35  #Subsume      : 3
% 2.46/1.35  #Demod        : 47
% 2.46/1.35  #Tautology    : 41
% 2.46/1.35  #SimpNegUnit  : 5
% 2.46/1.35  #BackRed      : 12
% 2.46/1.35  
% 2.46/1.35  #Partial instantiations: 0
% 2.46/1.35  #Strategies tried      : 1
% 2.46/1.35  
% 2.46/1.35  Timing (in seconds)
% 2.46/1.35  ----------------------
% 2.46/1.35  Preprocessing        : 0.35
% 2.46/1.35  Parsing              : 0.19
% 2.46/1.35  CNF conversion       : 0.02
% 2.46/1.35  Main loop            : 0.21
% 2.46/1.35  Inferencing          : 0.07
% 2.46/1.35  Reduction            : 0.07
% 2.46/1.35  Demodulation         : 0.05
% 2.46/1.35  BG Simplification    : 0.02
% 2.46/1.35  Subsumption          : 0.03
% 2.46/1.35  Abstraction          : 0.01
% 2.46/1.35  MUC search           : 0.00
% 2.46/1.35  Cooper               : 0.00
% 2.46/1.35  Total                : 0.59
% 2.46/1.35  Index Insertion      : 0.00
% 2.46/1.35  Index Deletion       : 0.00
% 2.46/1.35  Index Matching       : 0.00
% 2.46/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
