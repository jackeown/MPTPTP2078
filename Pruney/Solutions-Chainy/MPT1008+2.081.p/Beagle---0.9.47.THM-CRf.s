%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:37 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 174 expanded)
%              Number of leaves         :   34 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :   94 ( 414 expanded)
%              Number of equality atoms :   51 ( 203 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_79,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_65,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_69,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_65])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_89,plain,(
    ! [A_40,B_41,C_42] :
      ( k1_relset_1(A_40,B_41,C_42) = k1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_93,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_89])).

tff(c_123,plain,(
    ! [B_56,A_57,C_58] :
      ( k1_xboole_0 = B_56
      | k1_relset_1(A_57,B_56,C_58) = A_57
      | ~ v1_funct_2(C_58,A_57,B_56)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_126,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_123])).

tff(c_129,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_93,c_126])).

tff(c_130,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_129])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k1_tarski(k1_funct_1(B_9,A_8)) = k2_relat_1(B_9)
      | k1_tarski(A_8) != k1_relat_1(B_9)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_7] :
      ( k9_relat_1(A_7,k1_relat_1(A_7)) = k2_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( k7_relset_1(A_45,B_46,C_47,D_48) = k9_relat_1(C_47,D_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_110,plain,(
    ! [D_48] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',D_48) = k9_relat_1('#skF_3',D_48) ),
    inference(resolution,[status(thm)],[c_42,c_107])).

tff(c_131,plain,(
    ! [D_48] : k7_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3',D_48) = k9_relat_1('#skF_3',D_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_110])).

tff(c_135,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_44])).

tff(c_134,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_42])).

tff(c_207,plain,(
    ! [B_71,A_72,C_73] :
      ( k1_xboole_0 = B_71
      | k8_relset_1(A_72,B_71,C_73,B_71) = A_72
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71)))
      | ~ v1_funct_2(C_73,A_72,B_71)
      | ~ v1_funct_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_209,plain,
    ( k1_xboole_0 = '#skF_2'
    | k8_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_134,c_207])).

tff(c_212,plain,
    ( k1_xboole_0 = '#skF_2'
    | k8_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_135,c_209])).

tff(c_213,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_212])).

tff(c_183,plain,(
    ! [B_65,A_66,C_67] :
      ( k7_relset_1(B_65,A_66,C_67,k8_relset_1(B_65,A_66,C_67,A_66)) = k2_relset_1(B_65,A_66,C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(B_65,A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_186,plain,(
    k7_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3',k8_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3','#skF_2')) = k2_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_134,c_183])).

tff(c_215,plain,(
    k7_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3',k1_relat_1('#skF_3')) = k2_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_186])).

tff(c_216,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k9_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_215])).

tff(c_38,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_133,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_38])).

tff(c_221,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_133])).

tff(c_228,plain,
    ( k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_221])).

tff(c_230,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_228])).

tff(c_242,plain,
    ( k1_tarski('#skF_1') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_230])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_46,c_130,c_242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.25  
% 2.22/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.25  %$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.22/1.25  
% 2.22/1.25  %Foreground sorts:
% 2.22/1.25  
% 2.22/1.25  
% 2.22/1.25  %Background operators:
% 2.22/1.25  
% 2.22/1.25  
% 2.22/1.25  %Foreground operators:
% 2.22/1.25  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.22/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.22/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.22/1.25  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.22/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.25  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.22/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.22/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.25  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.22/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.22/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.22/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.22/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.25  
% 2.22/1.27  tff(f_103, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 2.22/1.27  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.22/1.27  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.22/1.27  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.22/1.27  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.22/1.27  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.22/1.27  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.22/1.27  tff(f_91, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 2.22/1.27  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 2.22/1.27  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.22/1.27  tff(c_65, plain, (![C_32, A_33, B_34]: (v1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.22/1.27  tff(c_69, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_65])).
% 2.22/1.27  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.22/1.27  tff(c_40, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.22/1.27  tff(c_44, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.22/1.27  tff(c_89, plain, (![A_40, B_41, C_42]: (k1_relset_1(A_40, B_41, C_42)=k1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.22/1.27  tff(c_93, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_89])).
% 2.22/1.27  tff(c_123, plain, (![B_56, A_57, C_58]: (k1_xboole_0=B_56 | k1_relset_1(A_57, B_56, C_58)=A_57 | ~v1_funct_2(C_58, A_57, B_56) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.22/1.27  tff(c_126, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_42, c_123])).
% 2.22/1.27  tff(c_129, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_93, c_126])).
% 2.22/1.27  tff(c_130, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_129])).
% 2.22/1.27  tff(c_10, plain, (![B_9, A_8]: (k1_tarski(k1_funct_1(B_9, A_8))=k2_relat_1(B_9) | k1_tarski(A_8)!=k1_relat_1(B_9) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.27  tff(c_8, plain, (![A_7]: (k9_relat_1(A_7, k1_relat_1(A_7))=k2_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.27  tff(c_107, plain, (![A_45, B_46, C_47, D_48]: (k7_relset_1(A_45, B_46, C_47, D_48)=k9_relat_1(C_47, D_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.22/1.27  tff(c_110, plain, (![D_48]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', D_48)=k9_relat_1('#skF_3', D_48))), inference(resolution, [status(thm)], [c_42, c_107])).
% 2.22/1.27  tff(c_131, plain, (![D_48]: (k7_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3', D_48)=k9_relat_1('#skF_3', D_48))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_110])).
% 2.22/1.27  tff(c_135, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_44])).
% 2.22/1.27  tff(c_134, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_42])).
% 2.22/1.27  tff(c_207, plain, (![B_71, A_72, C_73]: (k1_xboole_0=B_71 | k8_relset_1(A_72, B_71, C_73, B_71)=A_72 | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_72, B_71))) | ~v1_funct_2(C_73, A_72, B_71) | ~v1_funct_1(C_73))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.22/1.27  tff(c_209, plain, (k1_xboole_0='#skF_2' | k8_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_134, c_207])).
% 2.22/1.27  tff(c_212, plain, (k1_xboole_0='#skF_2' | k8_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_135, c_209])).
% 2.22/1.27  tff(c_213, plain, (k8_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_212])).
% 2.22/1.27  tff(c_183, plain, (![B_65, A_66, C_67]: (k7_relset_1(B_65, A_66, C_67, k8_relset_1(B_65, A_66, C_67, A_66))=k2_relset_1(B_65, A_66, C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(B_65, A_66))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.22/1.27  tff(c_186, plain, (k7_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3', k8_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3', '#skF_2'))=k2_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_134, c_183])).
% 2.22/1.27  tff(c_215, plain, (k7_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3', k1_relat_1('#skF_3'))=k2_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_186])).
% 2.22/1.27  tff(c_216, plain, (k2_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k9_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_215])).
% 2.22/1.27  tff(c_38, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.22/1.27  tff(c_133, plain, (k2_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_38])).
% 2.22/1.27  tff(c_221, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_133])).
% 2.22/1.27  tff(c_228, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_221])).
% 2.22/1.27  tff(c_230, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_228])).
% 2.22/1.27  tff(c_242, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_230])).
% 2.22/1.27  tff(c_246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_46, c_130, c_242])).
% 2.22/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.27  
% 2.22/1.27  Inference rules
% 2.22/1.27  ----------------------
% 2.22/1.27  #Ref     : 0
% 2.22/1.27  #Sup     : 47
% 2.22/1.27  #Fact    : 0
% 2.22/1.27  #Define  : 0
% 2.22/1.27  #Split   : 0
% 2.22/1.27  #Chain   : 0
% 2.22/1.27  #Close   : 0
% 2.22/1.27  
% 2.22/1.27  Ordering : KBO
% 2.22/1.27  
% 2.22/1.27  Simplification rules
% 2.22/1.27  ----------------------
% 2.22/1.27  #Subsume      : 0
% 2.22/1.27  #Demod        : 28
% 2.22/1.27  #Tautology    : 36
% 2.22/1.27  #SimpNegUnit  : 4
% 2.22/1.27  #BackRed      : 8
% 2.22/1.27  
% 2.22/1.27  #Partial instantiations: 0
% 2.22/1.27  #Strategies tried      : 1
% 2.22/1.27  
% 2.22/1.27  Timing (in seconds)
% 2.22/1.27  ----------------------
% 2.22/1.27  Preprocessing        : 0.32
% 2.22/1.27  Parsing              : 0.17
% 2.22/1.27  CNF conversion       : 0.02
% 2.22/1.27  Main loop            : 0.18
% 2.22/1.27  Inferencing          : 0.07
% 2.22/1.27  Reduction            : 0.06
% 2.22/1.27  Demodulation         : 0.04
% 2.22/1.27  BG Simplification    : 0.02
% 2.22/1.27  Subsumption          : 0.03
% 2.22/1.27  Abstraction          : 0.01
% 2.22/1.27  MUC search           : 0.00
% 2.22/1.27  Cooper               : 0.00
% 2.22/1.27  Total                : 0.54
% 2.22/1.27  Index Insertion      : 0.00
% 2.22/1.27  Index Deletion       : 0.00
% 2.22/1.27  Index Matching       : 0.00
% 2.22/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
