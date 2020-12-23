%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:50 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 105 expanded)
%              Number of leaves         :   35 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   92 ( 248 expanded)
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

tff(f_103,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_83,axiom,(
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

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_45,axiom,(
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

tff(c_56,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_85,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k7_relset_1(A_79,B_80,C_81,D_82) = k9_relat_1(C_81,D_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_88,plain,(
    ! [D_82] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_82) = k9_relat_1('#skF_8',D_82) ),
    inference(resolution,[status(thm)],[c_56,c_85])).

tff(c_46,plain,(
    ~ r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_89,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_46])).

tff(c_22,plain,(
    ! [A_46,B_47] : v1_relat_1(k2_zfmisc_1(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_66,plain,(
    ! [B_67,A_68] :
      ( v1_relat_1(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_56,c_66])).

tff(c_72,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_69])).

tff(c_52,plain,(
    r2_hidden('#skF_10','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_58,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_74,plain,(
    ! [A_70,B_71,C_72] :
      ( k1_relset_1(A_70,B_71,C_72) = k1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_78,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_74])).

tff(c_170,plain,(
    ! [B_108,A_109,C_110] :
      ( k1_xboole_0 = B_108
      | k1_relset_1(A_109,B_108,C_110) = A_109
      | ~ v1_funct_2(C_110,A_109,B_108)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_173,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_170])).

tff(c_176,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_78,c_173])).

tff(c_177,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_176])).

tff(c_60,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_48,plain,(
    k1_funct_1('#skF_8','#skF_10') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_102,plain,(
    ! [A_90,C_91] :
      ( r2_hidden(k4_tarski(A_90,k1_funct_1(C_91,A_90)),C_91)
      | ~ r2_hidden(A_90,k1_relat_1(C_91))
      | ~ v1_funct_1(C_91)
      | ~ v1_relat_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_111,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_102])).

tff(c_116,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_60,c_111])).

tff(c_117,plain,(
    ~ r2_hidden('#skF_10',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_178,plain,(
    ~ r2_hidden('#skF_10','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_117])).

tff(c_182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_178])).

tff(c_183,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_50,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_185,plain,(
    ! [D_111,A_112,B_113,E_114] :
      ( r2_hidden(D_111,k9_relat_1(A_112,B_113))
      | ~ r2_hidden(E_114,B_113)
      | ~ r2_hidden(k4_tarski(E_114,D_111),A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_213,plain,(
    ! [D_115,A_116] :
      ( r2_hidden(D_115,k9_relat_1(A_116,'#skF_7'))
      | ~ r2_hidden(k4_tarski('#skF_10',D_115),A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(resolution,[status(thm)],[c_50,c_185])).

tff(c_216,plain,
    ( r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_183,c_213])).

tff(c_223,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_216])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_223])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:54:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.30  
% 2.12/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.30  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.33/1.30  
% 2.33/1.30  %Foreground sorts:
% 2.33/1.30  
% 2.33/1.30  
% 2.33/1.30  %Background operators:
% 2.33/1.30  
% 2.33/1.30  
% 2.33/1.30  %Foreground operators:
% 2.33/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.33/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.33/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.33/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.33/1.30  tff('#skF_10', type, '#skF_10': $i).
% 2.33/1.30  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.33/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.33/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.33/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.33/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.33/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.33/1.30  tff('#skF_9', type, '#skF_9': $i).
% 2.33/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.33/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.33/1.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.33/1.30  tff('#skF_8', type, '#skF_8': $i).
% 2.33/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.33/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.33/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.33/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.30  
% 2.33/1.32  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => (![E]: ((?[F]: ((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))) => r2_hidden(E, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_2)).
% 2.33/1.32  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.33/1.32  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.33/1.32  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.33/1.32  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.33/1.32  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.33/1.32  tff(f_57, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.33/1.32  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 2.33/1.32  tff(c_56, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.33/1.32  tff(c_85, plain, (![A_79, B_80, C_81, D_82]: (k7_relset_1(A_79, B_80, C_81, D_82)=k9_relat_1(C_81, D_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.33/1.32  tff(c_88, plain, (![D_82]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_82)=k9_relat_1('#skF_8', D_82))), inference(resolution, [status(thm)], [c_56, c_85])).
% 2.33/1.32  tff(c_46, plain, (~r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.33/1.32  tff(c_89, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_46])).
% 2.33/1.32  tff(c_22, plain, (![A_46, B_47]: (v1_relat_1(k2_zfmisc_1(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.33/1.32  tff(c_66, plain, (![B_67, A_68]: (v1_relat_1(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.33/1.32  tff(c_69, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_56, c_66])).
% 2.33/1.32  tff(c_72, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_69])).
% 2.33/1.32  tff(c_52, plain, (r2_hidden('#skF_10', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.33/1.32  tff(c_54, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.33/1.32  tff(c_58, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.33/1.32  tff(c_74, plain, (![A_70, B_71, C_72]: (k1_relset_1(A_70, B_71, C_72)=k1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.33/1.32  tff(c_78, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_74])).
% 2.33/1.32  tff(c_170, plain, (![B_108, A_109, C_110]: (k1_xboole_0=B_108 | k1_relset_1(A_109, B_108, C_110)=A_109 | ~v1_funct_2(C_110, A_109, B_108) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.33/1.32  tff(c_173, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_170])).
% 2.33/1.32  tff(c_176, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_78, c_173])).
% 2.33/1.32  tff(c_177, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_54, c_176])).
% 2.33/1.32  tff(c_60, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.33/1.32  tff(c_48, plain, (k1_funct_1('#skF_8', '#skF_10')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.33/1.32  tff(c_102, plain, (![A_90, C_91]: (r2_hidden(k4_tarski(A_90, k1_funct_1(C_91, A_90)), C_91) | ~r2_hidden(A_90, k1_relat_1(C_91)) | ~v1_funct_1(C_91) | ~v1_relat_1(C_91))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.33/1.32  tff(c_111, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_48, c_102])).
% 2.33/1.32  tff(c_116, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_60, c_111])).
% 2.33/1.32  tff(c_117, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_116])).
% 2.33/1.32  tff(c_178, plain, (~r2_hidden('#skF_10', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_117])).
% 2.33/1.32  tff(c_182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_178])).
% 2.33/1.32  tff(c_183, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_116])).
% 2.33/1.32  tff(c_50, plain, (r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.33/1.32  tff(c_185, plain, (![D_111, A_112, B_113, E_114]: (r2_hidden(D_111, k9_relat_1(A_112, B_113)) | ~r2_hidden(E_114, B_113) | ~r2_hidden(k4_tarski(E_114, D_111), A_112) | ~v1_relat_1(A_112))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.33/1.32  tff(c_213, plain, (![D_115, A_116]: (r2_hidden(D_115, k9_relat_1(A_116, '#skF_7')) | ~r2_hidden(k4_tarski('#skF_10', D_115), A_116) | ~v1_relat_1(A_116))), inference(resolution, [status(thm)], [c_50, c_185])).
% 2.33/1.32  tff(c_216, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_183, c_213])).
% 2.33/1.32  tff(c_223, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_216])).
% 2.33/1.32  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_223])).
% 2.33/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.32  
% 2.33/1.32  Inference rules
% 2.33/1.32  ----------------------
% 2.33/1.32  #Ref     : 0
% 2.33/1.32  #Sup     : 33
% 2.33/1.32  #Fact    : 0
% 2.33/1.32  #Define  : 0
% 2.33/1.32  #Split   : 1
% 2.33/1.32  #Chain   : 0
% 2.33/1.32  #Close   : 0
% 2.33/1.32  
% 2.33/1.32  Ordering : KBO
% 2.33/1.32  
% 2.33/1.32  Simplification rules
% 2.33/1.32  ----------------------
% 2.33/1.32  #Subsume      : 2
% 2.33/1.32  #Demod        : 22
% 2.33/1.32  #Tautology    : 11
% 2.33/1.32  #SimpNegUnit  : 4
% 2.33/1.32  #BackRed      : 3
% 2.33/1.32  
% 2.33/1.32  #Partial instantiations: 0
% 2.33/1.32  #Strategies tried      : 1
% 2.33/1.32  
% 2.33/1.32  Timing (in seconds)
% 2.33/1.32  ----------------------
% 2.33/1.32  Preprocessing        : 0.33
% 2.33/1.32  Parsing              : 0.16
% 2.33/1.32  CNF conversion       : 0.03
% 2.33/1.32  Main loop            : 0.21
% 2.33/1.32  Inferencing          : 0.07
% 2.33/1.32  Reduction            : 0.06
% 2.33/1.32  Demodulation         : 0.05
% 2.33/1.32  BG Simplification    : 0.02
% 2.33/1.32  Subsumption          : 0.04
% 2.33/1.32  Abstraction          : 0.01
% 2.33/1.32  MUC search           : 0.00
% 2.33/1.32  Cooper               : 0.00
% 2.33/1.32  Total                : 0.57
% 2.33/1.32  Index Insertion      : 0.00
% 2.33/1.32  Index Deletion       : 0.00
% 2.33/1.32  Index Matching       : 0.00
% 2.33/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
