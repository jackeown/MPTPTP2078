%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:25 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 515 expanded)
%              Number of leaves         :   28 ( 184 expanded)
%              Depth                    :   12
%              Number of atoms          :  116 (1130 expanded)
%              Number of equality atoms :   29 ( 233 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_49,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_58,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_62,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_58])).

tff(c_68,plain,(
    ! [A_47,B_48,C_49] :
      ( k1_relset_1(A_47,B_48,C_49) = k1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_72,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_68])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [D_38] :
      ( ~ r2_hidden(D_38,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_38,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_53,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3')
    | v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_48])).

tff(c_85,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3')
    | v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_53])).

tff(c_86,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_97,plain,(
    ! [A_54,B_55,C_56] :
      ( m1_subset_1(k1_relset_1(A_54,B_55,C_56),k1_zfmisc_1(A_54))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_114,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_97])).

tff(c_120,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_114])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( m1_subset_1(A_6,C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_124,plain,(
    ! [A_57] :
      ( m1_subset_1(A_57,'#skF_3')
      | ~ r2_hidden(A_57,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_120,c_8])).

tff(c_128,plain,
    ( m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3')
    | v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_124])).

tff(c_131,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_128])).

tff(c_10,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k1_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_134,plain,
    ( ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_131,c_10])).

tff(c_140,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_134])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_160,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_140,c_6])).

tff(c_87,plain,(
    ! [A_51,B_52,C_53] :
      ( k2_relset_1(A_51,B_52,C_53) = k2_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_91,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_87])).

tff(c_26,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_92,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_26])).

tff(c_168,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_92])).

tff(c_12,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_170,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_160,c_12])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_170])).

tff(c_193,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_197,plain,
    ( ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_193,c_10])).

tff(c_203,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_197])).

tff(c_208,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_203,c_6])).

tff(c_204,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_193,c_6])).

tff(c_217,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_204])).

tff(c_194,plain,(
    m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_218,plain,(
    m1_subset_1('#skF_1'('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_194])).

tff(c_24,plain,(
    ! [D_33] :
      ( ~ r2_hidden(D_33,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_33,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_78,plain,(
    ! [D_50] :
      ( ~ r2_hidden(D_50,k1_relat_1('#skF_4'))
      | ~ m1_subset_1(D_50,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_24])).

tff(c_83,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3')
    | v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_78])).

tff(c_84,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_217,c_84])).

tff(c_251,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_257,plain,
    ( ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_251,c_10])).

tff(c_263,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_257])).

tff(c_268,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_263,c_6])).

tff(c_264,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_251,c_6])).

tff(c_277,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_264])).

tff(c_253,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3')
    | v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_53])).

tff(c_254,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_308,plain,(
    ~ m1_subset_1('#skF_1'('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_254])).

tff(c_252,plain,(
    m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_309,plain,(
    m1_subset_1('#skF_1'('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_252])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_308,c_309])).

tff(c_311,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_315,plain,
    ( ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_311,c_10])).

tff(c_321,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_315])).

tff(c_326,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_321,c_6])).

tff(c_327,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_26])).

tff(c_329,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_326,c_12])).

tff(c_336,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(A_70,B_71,C_72) = k2_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_340,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_336])).

tff(c_372,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_340])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:26:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.32  
% 2.37/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.32  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.37/1.32  
% 2.37/1.32  %Foreground sorts:
% 2.37/1.32  
% 2.37/1.32  
% 2.37/1.32  %Background operators:
% 2.37/1.32  
% 2.37/1.32  
% 2.37/1.32  %Foreground operators:
% 2.37/1.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.37/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.37/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.37/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.37/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.37/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.37/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.32  
% 2.37/1.34  tff(f_89, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 2.37/1.34  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.37/1.34  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.37/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.37/1.34  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.37/1.34  tff(f_41, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.37/1.34  tff(f_49, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.37/1.34  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 2.37/1.34  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.37/1.34  tff(f_52, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.37/1.34  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.37/1.34  tff(c_58, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.37/1.34  tff(c_62, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_58])).
% 2.37/1.34  tff(c_68, plain, (![A_47, B_48, C_49]: (k1_relset_1(A_47, B_48, C_49)=k1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.37/1.34  tff(c_72, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_68])).
% 2.37/1.34  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.37/1.34  tff(c_48, plain, (![D_38]: (~r2_hidden(D_38, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_38, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.37/1.34  tff(c_53, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3') | v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_48])).
% 2.37/1.34  tff(c_85, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3') | v1_xboole_0(k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_53])).
% 2.37/1.34  tff(c_86, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_85])).
% 2.37/1.34  tff(c_97, plain, (![A_54, B_55, C_56]: (m1_subset_1(k1_relset_1(A_54, B_55, C_56), k1_zfmisc_1(A_54)) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.37/1.34  tff(c_114, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_72, c_97])).
% 2.37/1.34  tff(c_120, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_114])).
% 2.37/1.34  tff(c_8, plain, (![A_6, C_8, B_7]: (m1_subset_1(A_6, C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.37/1.34  tff(c_124, plain, (![A_57]: (m1_subset_1(A_57, '#skF_3') | ~r2_hidden(A_57, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_120, c_8])).
% 2.37/1.34  tff(c_128, plain, (m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3') | v1_xboole_0(k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_124])).
% 2.37/1.34  tff(c_131, plain, (v1_xboole_0(k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_86, c_128])).
% 2.37/1.34  tff(c_10, plain, (![A_9]: (~v1_xboole_0(k1_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.37/1.34  tff(c_134, plain, (~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_131, c_10])).
% 2.37/1.34  tff(c_140, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_134])).
% 2.37/1.34  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.37/1.34  tff(c_160, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_140, c_6])).
% 2.37/1.34  tff(c_87, plain, (![A_51, B_52, C_53]: (k2_relset_1(A_51, B_52, C_53)=k2_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.37/1.34  tff(c_91, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_87])).
% 2.37/1.34  tff(c_26, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.37/1.34  tff(c_92, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_91, c_26])).
% 2.37/1.34  tff(c_168, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_92])).
% 2.37/1.34  tff(c_12, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.37/1.34  tff(c_170, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_160, c_12])).
% 2.37/1.34  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_170])).
% 2.37/1.34  tff(c_193, plain, (v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_85])).
% 2.37/1.34  tff(c_197, plain, (~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_193, c_10])).
% 2.37/1.34  tff(c_203, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_197])).
% 2.37/1.34  tff(c_208, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_203, c_6])).
% 2.37/1.34  tff(c_204, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_193, c_6])).
% 2.37/1.34  tff(c_217, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_208, c_204])).
% 2.37/1.34  tff(c_194, plain, (m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(splitRight, [status(thm)], [c_85])).
% 2.37/1.34  tff(c_218, plain, (m1_subset_1('#skF_1'('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_217, c_194])).
% 2.37/1.34  tff(c_24, plain, (![D_33]: (~r2_hidden(D_33, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_33, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.37/1.34  tff(c_78, plain, (![D_50]: (~r2_hidden(D_50, k1_relat_1('#skF_4')) | ~m1_subset_1(D_50, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_24])).
% 2.37/1.34  tff(c_83, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3') | v1_xboole_0(k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_78])).
% 2.37/1.34  tff(c_84, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_83])).
% 2.37/1.34  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_218, c_217, c_84])).
% 2.37/1.34  tff(c_251, plain, (v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_83])).
% 2.37/1.34  tff(c_257, plain, (~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_251, c_10])).
% 2.37/1.34  tff(c_263, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_257])).
% 2.37/1.34  tff(c_268, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_263, c_6])).
% 2.37/1.34  tff(c_264, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_251, c_6])).
% 2.37/1.34  tff(c_277, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_268, c_264])).
% 2.37/1.34  tff(c_253, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3') | v1_xboole_0(k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_53])).
% 2.37/1.34  tff(c_254, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_253])).
% 2.37/1.34  tff(c_308, plain, (~m1_subset_1('#skF_1'('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_277, c_254])).
% 2.37/1.34  tff(c_252, plain, (m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(splitRight, [status(thm)], [c_83])).
% 2.37/1.34  tff(c_309, plain, (m1_subset_1('#skF_1'('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_277, c_252])).
% 2.37/1.34  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_308, c_309])).
% 2.37/1.34  tff(c_311, plain, (v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_253])).
% 2.37/1.34  tff(c_315, plain, (~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_311, c_10])).
% 2.37/1.34  tff(c_321, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_315])).
% 2.37/1.34  tff(c_326, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_321, c_6])).
% 2.37/1.34  tff(c_327, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_326, c_26])).
% 2.37/1.34  tff(c_329, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_326, c_326, c_12])).
% 2.37/1.34  tff(c_336, plain, (![A_70, B_71, C_72]: (k2_relset_1(A_70, B_71, C_72)=k2_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.37/1.34  tff(c_340, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_336])).
% 2.37/1.34  tff(c_372, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_329, c_340])).
% 2.37/1.34  tff(c_373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_327, c_372])).
% 2.37/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.34  
% 2.37/1.34  Inference rules
% 2.37/1.34  ----------------------
% 2.37/1.34  #Ref     : 0
% 2.37/1.34  #Sup     : 74
% 2.37/1.34  #Fact    : 0
% 2.37/1.34  #Define  : 0
% 2.37/1.34  #Split   : 3
% 2.37/1.34  #Chain   : 0
% 2.37/1.34  #Close   : 0
% 2.37/1.34  
% 2.37/1.34  Ordering : KBO
% 2.37/1.34  
% 2.37/1.34  Simplification rules
% 2.37/1.34  ----------------------
% 2.37/1.34  #Subsume      : 1
% 2.37/1.34  #Demod        : 88
% 2.37/1.34  #Tautology    : 54
% 2.37/1.34  #SimpNegUnit  : 4
% 2.37/1.34  #BackRed      : 36
% 2.37/1.34  
% 2.37/1.34  #Partial instantiations: 0
% 2.37/1.34  #Strategies tried      : 1
% 2.37/1.34  
% 2.37/1.34  Timing (in seconds)
% 2.37/1.34  ----------------------
% 2.37/1.34  Preprocessing        : 0.28
% 2.37/1.34  Parsing              : 0.15
% 2.37/1.34  CNF conversion       : 0.02
% 2.37/1.34  Main loop            : 0.22
% 2.37/1.34  Inferencing          : 0.08
% 2.37/1.34  Reduction            : 0.07
% 2.37/1.34  Demodulation         : 0.05
% 2.37/1.34  BG Simplification    : 0.01
% 2.37/1.34  Subsumption          : 0.03
% 2.37/1.34  Abstraction          : 0.01
% 2.37/1.34  MUC search           : 0.00
% 2.37/1.34  Cooper               : 0.00
% 2.37/1.34  Total                : 0.54
% 2.37/1.34  Index Insertion      : 0.00
% 2.37/1.34  Index Deletion       : 0.00
% 2.37/1.34  Index Matching       : 0.00
% 2.37/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
