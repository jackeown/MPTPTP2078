%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:50 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 111 expanded)
%              Number of leaves         :   31 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :   99 ( 302 expanded)
%              Number of equality atoms :   31 (  81 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( B != k1_xboole_0
         => ! [E] :
              ( ? [F] :
                  ( r2_hidden(F,A)
                  & r2_hidden(F,C)
                  & E = k1_funct_1(D,F) )
             => r2_hidden(E,k7_relset_1(A,B,D,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_2)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_76,axiom,(
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

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_71,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( k7_relset_1(A_43,B_44,C_45,D_46) = k9_relat_1(C_45,D_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_74,plain,(
    ! [D_46] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_46) = k9_relat_1('#skF_5',D_46) ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_75,plain,(
    ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_34])).

tff(c_53,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_57,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_53])).

tff(c_40,plain,(
    r2_hidden('#skF_7','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_46,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_58,plain,(
    ! [A_30,B_31,C_32] :
      ( k1_relset_1(A_30,B_31,C_32) = k1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_62,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_58])).

tff(c_175,plain,(
    ! [B_76,A_77,C_78] :
      ( k1_xboole_0 = B_76
      | k1_relset_1(A_77,B_76,C_78) = A_77
      | ~ v1_funct_2(C_78,A_77,B_76)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_178,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_175])).

tff(c_181,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_62,c_178])).

tff(c_182,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_181])).

tff(c_134,plain,(
    ! [B_68,A_69,C_70] :
      ( k1_xboole_0 = B_68
      | k1_relset_1(A_69,B_68,C_70) = A_69
      | ~ v1_funct_2(C_70,A_69,B_68)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_137,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_134])).

tff(c_140,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_62,c_137])).

tff(c_141,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_140])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36,plain,(
    k1_funct_1('#skF_5','#skF_7') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_97,plain,(
    ! [A_58,C_59] :
      ( r2_hidden(k4_tarski(A_58,k1_funct_1(C_59,A_58)),C_59)
      | ~ r2_hidden(A_58,k1_relat_1(C_59))
      | ~ v1_funct_1(C_59)
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_106,plain,
    ( r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_97])).

tff(c_111,plain,
    ( r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_48,c_106])).

tff(c_112,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_142,plain,(
    ~ r2_hidden('#skF_7','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_112])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_142])).

tff(c_147,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_38,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_208,plain,(
    ! [A_84,C_85,B_86,D_87] :
      ( r2_hidden(A_84,k9_relat_1(C_85,B_86))
      | ~ r2_hidden(D_87,B_86)
      | ~ r2_hidden(k4_tarski(D_87,A_84),C_85)
      | ~ r2_hidden(D_87,k1_relat_1(C_85))
      | ~ v1_relat_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_233,plain,(
    ! [A_88,C_89] :
      ( r2_hidden(A_88,k9_relat_1(C_89,'#skF_4'))
      | ~ r2_hidden(k4_tarski('#skF_7',A_88),C_89)
      | ~ r2_hidden('#skF_7',k1_relat_1(C_89))
      | ~ v1_relat_1(C_89) ) ),
    inference(resolution,[status(thm)],[c_38,c_208])).

tff(c_236,plain,
    ( r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_147,c_233])).

tff(c_243,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_40,c_182,c_236])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:24:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.27  
% 2.21/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.27  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.21/1.27  
% 2.21/1.27  %Foreground sorts:
% 2.21/1.27  
% 2.21/1.27  
% 2.21/1.27  %Background operators:
% 2.21/1.27  
% 2.21/1.27  
% 2.21/1.27  %Foreground operators:
% 2.21/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.21/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.21/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.21/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.27  tff('#skF_7', type, '#skF_7': $i).
% 2.21/1.27  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.21/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.21/1.27  tff('#skF_6', type, '#skF_6': $i).
% 2.21/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.21/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.21/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.21/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.27  
% 2.21/1.29  tff(f_96, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => (![E]: ((?[F]: ((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))) => r2_hidden(E, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_2)).
% 2.21/1.29  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.21/1.29  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.21/1.29  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.21/1.29  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.21/1.29  tff(f_46, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.21/1.29  tff(f_36, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.21/1.29  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.21/1.29  tff(c_71, plain, (![A_43, B_44, C_45, D_46]: (k7_relset_1(A_43, B_44, C_45, D_46)=k9_relat_1(C_45, D_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.21/1.29  tff(c_74, plain, (![D_46]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_46)=k9_relat_1('#skF_5', D_46))), inference(resolution, [status(thm)], [c_44, c_71])).
% 2.21/1.29  tff(c_34, plain, (~r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.21/1.29  tff(c_75, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_34])).
% 2.21/1.29  tff(c_53, plain, (![C_27, A_28, B_29]: (v1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.21/1.29  tff(c_57, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_53])).
% 2.21/1.29  tff(c_40, plain, (r2_hidden('#skF_7', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.21/1.29  tff(c_42, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.21/1.29  tff(c_46, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.21/1.29  tff(c_58, plain, (![A_30, B_31, C_32]: (k1_relset_1(A_30, B_31, C_32)=k1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.21/1.29  tff(c_62, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_58])).
% 2.21/1.29  tff(c_175, plain, (![B_76, A_77, C_78]: (k1_xboole_0=B_76 | k1_relset_1(A_77, B_76, C_78)=A_77 | ~v1_funct_2(C_78, A_77, B_76) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.21/1.29  tff(c_178, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_175])).
% 2.21/1.29  tff(c_181, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_62, c_178])).
% 2.21/1.29  tff(c_182, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_42, c_181])).
% 2.21/1.29  tff(c_134, plain, (![B_68, A_69, C_70]: (k1_xboole_0=B_68 | k1_relset_1(A_69, B_68, C_70)=A_69 | ~v1_funct_2(C_70, A_69, B_68) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.21/1.29  tff(c_137, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_134])).
% 2.21/1.29  tff(c_140, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_62, c_137])).
% 2.21/1.29  tff(c_141, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_42, c_140])).
% 2.21/1.29  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.21/1.29  tff(c_36, plain, (k1_funct_1('#skF_5', '#skF_7')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.21/1.29  tff(c_97, plain, (![A_58, C_59]: (r2_hidden(k4_tarski(A_58, k1_funct_1(C_59, A_58)), C_59) | ~r2_hidden(A_58, k1_relat_1(C_59)) | ~v1_funct_1(C_59) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.21/1.29  tff(c_106, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_36, c_97])).
% 2.21/1.29  tff(c_111, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_7', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_48, c_106])).
% 2.21/1.29  tff(c_112, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_111])).
% 2.21/1.29  tff(c_142, plain, (~r2_hidden('#skF_7', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_112])).
% 2.21/1.29  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_142])).
% 2.21/1.29  tff(c_147, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_111])).
% 2.21/1.29  tff(c_38, plain, (r2_hidden('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.21/1.29  tff(c_208, plain, (![A_84, C_85, B_86, D_87]: (r2_hidden(A_84, k9_relat_1(C_85, B_86)) | ~r2_hidden(D_87, B_86) | ~r2_hidden(k4_tarski(D_87, A_84), C_85) | ~r2_hidden(D_87, k1_relat_1(C_85)) | ~v1_relat_1(C_85))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.21/1.29  tff(c_233, plain, (![A_88, C_89]: (r2_hidden(A_88, k9_relat_1(C_89, '#skF_4')) | ~r2_hidden(k4_tarski('#skF_7', A_88), C_89) | ~r2_hidden('#skF_7', k1_relat_1(C_89)) | ~v1_relat_1(C_89))), inference(resolution, [status(thm)], [c_38, c_208])).
% 2.21/1.29  tff(c_236, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_147, c_233])).
% 2.21/1.29  tff(c_243, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_40, c_182, c_236])).
% 2.21/1.29  tff(c_245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_243])).
% 2.21/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.29  
% 2.21/1.29  Inference rules
% 2.21/1.29  ----------------------
% 2.21/1.29  #Ref     : 0
% 2.21/1.29  #Sup     : 41
% 2.21/1.29  #Fact    : 0
% 2.21/1.29  #Define  : 0
% 2.21/1.29  #Split   : 1
% 2.21/1.29  #Chain   : 0
% 2.21/1.29  #Close   : 0
% 2.21/1.29  
% 2.21/1.29  Ordering : KBO
% 2.21/1.29  
% 2.21/1.29  Simplification rules
% 2.21/1.29  ----------------------
% 2.21/1.29  #Subsume      : 1
% 2.21/1.29  #Demod        : 27
% 2.21/1.29  #Tautology    : 17
% 2.21/1.29  #SimpNegUnit  : 5
% 2.21/1.29  #BackRed      : 5
% 2.21/1.29  
% 2.21/1.29  #Partial instantiations: 0
% 2.21/1.29  #Strategies tried      : 1
% 2.21/1.29  
% 2.21/1.29  Timing (in seconds)
% 2.21/1.29  ----------------------
% 2.21/1.29  Preprocessing        : 0.34
% 2.21/1.29  Parsing              : 0.18
% 2.21/1.29  CNF conversion       : 0.02
% 2.21/1.29  Main loop            : 0.23
% 2.21/1.29  Inferencing          : 0.08
% 2.21/1.29  Reduction            : 0.07
% 2.21/1.29  Demodulation         : 0.05
% 2.21/1.29  BG Simplification    : 0.02
% 2.21/1.29  Subsumption          : 0.04
% 2.21/1.29  Abstraction          : 0.01
% 2.21/1.29  MUC search           : 0.00
% 2.21/1.29  Cooper               : 0.00
% 2.21/1.29  Total                : 0.60
% 2.21/1.29  Index Insertion      : 0.00
% 2.21/1.29  Index Deletion       : 0.00
% 2.21/1.29  Index Matching       : 0.00
% 2.21/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
