%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:49 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   65 (  96 expanded)
%              Number of leaves         :   34 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :   86 ( 230 expanded)
%              Number of equality atoms :   25 (  55 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_78,axiom,(
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

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_80,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k7_relset_1(A_76,B_77,C_78,D_79) = k9_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_83,plain,(
    ! [D_79] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_79) = k9_relat_1('#skF_8',D_79) ),
    inference(resolution,[status(thm)],[c_54,c_80])).

tff(c_44,plain,(
    ~ r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_84,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_44])).

tff(c_63,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_67,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_63])).

tff(c_50,plain,(
    r2_hidden('#skF_10','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_56,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_69,plain,(
    ! [A_67,B_68,C_69] :
      ( k1_relset_1(A_67,B_68,C_69) = k1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_73,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_69])).

tff(c_176,plain,(
    ! [B_108,A_109,C_110] :
      ( k1_xboole_0 = B_108
      | k1_relset_1(A_109,B_108,C_110) = A_109
      | ~ v1_funct_2(C_110,A_109,B_108)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_179,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_176])).

tff(c_182,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_73,c_179])).

tff(c_183,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_182])).

tff(c_58,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_46,plain,(
    k1_funct_1('#skF_8','#skF_10') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_104,plain,(
    ! [A_91,C_92] :
      ( r2_hidden(k4_tarski(A_91,k1_funct_1(C_92,A_91)),C_92)
      | ~ r2_hidden(A_91,k1_relat_1(C_92))
      | ~ v1_funct_1(C_92)
      | ~ v1_relat_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_123,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_104])).

tff(c_131,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_58,c_123])).

tff(c_132,plain,(
    ~ r2_hidden('#skF_10',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_184,plain,(
    ~ r2_hidden('#skF_10','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_132])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_184])).

tff(c_189,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_48,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_95,plain,(
    ! [D_83,A_84,B_85,E_86] :
      ( r2_hidden(D_83,k9_relat_1(A_84,B_85))
      | ~ r2_hidden(E_86,B_85)
      | ~ r2_hidden(k4_tarski(E_86,D_83),A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_100,plain,(
    ! [D_83,A_84] :
      ( r2_hidden(D_83,k9_relat_1(A_84,'#skF_7'))
      | ~ r2_hidden(k4_tarski('#skF_10',D_83),A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(resolution,[status(thm)],[c_48,c_95])).

tff(c_200,plain,
    ( r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_189,c_100])).

tff(c_214,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_200])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 16:01:15 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.26  
% 2.13/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.26  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.13/1.26  
% 2.13/1.26  %Foreground sorts:
% 2.13/1.26  
% 2.13/1.26  
% 2.13/1.26  %Background operators:
% 2.13/1.26  
% 2.13/1.26  
% 2.13/1.26  %Foreground operators:
% 2.13/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.13/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.13/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.26  tff('#skF_7', type, '#skF_7': $i).
% 2.13/1.26  tff('#skF_10', type, '#skF_10': $i).
% 2.13/1.26  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.13/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.13/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.13/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.13/1.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.13/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.13/1.26  tff('#skF_9', type, '#skF_9': $i).
% 2.13/1.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.13/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.13/1.26  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.13/1.26  tff('#skF_8', type, '#skF_8': $i).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.13/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.26  
% 2.13/1.27  tff(f_98, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => (![E]: ((?[F]: ((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))) => r2_hidden(E, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_2)).
% 2.13/1.27  tff(f_60, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.13/1.27  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.13/1.27  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.13/1.27  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.13/1.27  tff(f_48, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.13/1.27  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 2.13/1.27  tff(c_54, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.13/1.27  tff(c_80, plain, (![A_76, B_77, C_78, D_79]: (k7_relset_1(A_76, B_77, C_78, D_79)=k9_relat_1(C_78, D_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.13/1.27  tff(c_83, plain, (![D_79]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_79)=k9_relat_1('#skF_8', D_79))), inference(resolution, [status(thm)], [c_54, c_80])).
% 2.13/1.27  tff(c_44, plain, (~r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.13/1.27  tff(c_84, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_44])).
% 2.13/1.27  tff(c_63, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.13/1.27  tff(c_67, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_63])).
% 2.13/1.27  tff(c_50, plain, (r2_hidden('#skF_10', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.13/1.27  tff(c_52, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.13/1.27  tff(c_56, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.13/1.27  tff(c_69, plain, (![A_67, B_68, C_69]: (k1_relset_1(A_67, B_68, C_69)=k1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.13/1.27  tff(c_73, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_69])).
% 2.13/1.27  tff(c_176, plain, (![B_108, A_109, C_110]: (k1_xboole_0=B_108 | k1_relset_1(A_109, B_108, C_110)=A_109 | ~v1_funct_2(C_110, A_109, B_108) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.13/1.27  tff(c_179, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_176])).
% 2.13/1.27  tff(c_182, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_73, c_179])).
% 2.13/1.27  tff(c_183, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_52, c_182])).
% 2.13/1.27  tff(c_58, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.13/1.27  tff(c_46, plain, (k1_funct_1('#skF_8', '#skF_10')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.13/1.27  tff(c_104, plain, (![A_91, C_92]: (r2_hidden(k4_tarski(A_91, k1_funct_1(C_92, A_91)), C_92) | ~r2_hidden(A_91, k1_relat_1(C_92)) | ~v1_funct_1(C_92) | ~v1_relat_1(C_92))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.13/1.27  tff(c_123, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_46, c_104])).
% 2.13/1.27  tff(c_131, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_58, c_123])).
% 2.13/1.27  tff(c_132, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_131])).
% 2.13/1.27  tff(c_184, plain, (~r2_hidden('#skF_10', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_132])).
% 2.13/1.27  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_184])).
% 2.13/1.27  tff(c_189, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_131])).
% 2.13/1.27  tff(c_48, plain, (r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.13/1.27  tff(c_95, plain, (![D_83, A_84, B_85, E_86]: (r2_hidden(D_83, k9_relat_1(A_84, B_85)) | ~r2_hidden(E_86, B_85) | ~r2_hidden(k4_tarski(E_86, D_83), A_84) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.13/1.27  tff(c_100, plain, (![D_83, A_84]: (r2_hidden(D_83, k9_relat_1(A_84, '#skF_7')) | ~r2_hidden(k4_tarski('#skF_10', D_83), A_84) | ~v1_relat_1(A_84))), inference(resolution, [status(thm)], [c_48, c_95])).
% 2.13/1.27  tff(c_200, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_189, c_100])).
% 2.13/1.27  tff(c_214, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_200])).
% 2.13/1.27  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_214])).
% 2.13/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.27  
% 2.13/1.27  Inference rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Ref     : 0
% 2.13/1.27  #Sup     : 32
% 2.13/1.27  #Fact    : 0
% 2.13/1.27  #Define  : 0
% 2.13/1.27  #Split   : 1
% 2.13/1.27  #Chain   : 0
% 2.13/1.27  #Close   : 0
% 2.13/1.27  
% 2.13/1.27  Ordering : KBO
% 2.13/1.27  
% 2.13/1.27  Simplification rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Subsume      : 3
% 2.13/1.27  #Demod        : 18
% 2.13/1.27  #Tautology    : 9
% 2.13/1.27  #SimpNegUnit  : 4
% 2.13/1.27  #BackRed      : 3
% 2.13/1.27  
% 2.13/1.27  #Partial instantiations: 0
% 2.13/1.27  #Strategies tried      : 1
% 2.13/1.27  
% 2.13/1.27  Timing (in seconds)
% 2.13/1.27  ----------------------
% 2.13/1.27  Preprocessing        : 0.33
% 2.13/1.28  Parsing              : 0.17
% 2.13/1.28  CNF conversion       : 0.03
% 2.13/1.28  Main loop            : 0.19
% 2.13/1.28  Inferencing          : 0.06
% 2.13/1.28  Reduction            : 0.06
% 2.13/1.28  Demodulation         : 0.04
% 2.13/1.28  BG Simplification    : 0.02
% 2.13/1.28  Subsumption          : 0.03
% 2.32/1.28  Abstraction          : 0.01
% 2.32/1.28  MUC search           : 0.00
% 2.32/1.28  Cooper               : 0.00
% 2.32/1.28  Total                : 0.55
% 2.32/1.28  Index Insertion      : 0.00
% 2.32/1.28  Index Deletion       : 0.00
% 2.32/1.28  Index Matching       : 0.00
% 2.32/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
