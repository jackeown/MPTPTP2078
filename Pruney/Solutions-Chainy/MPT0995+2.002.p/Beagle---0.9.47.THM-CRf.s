%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:49 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 152 expanded)
%              Number of leaves         :   34 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 439 expanded)
%              Number of equality atoms :   33 ( 108 expanded)
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

tff(f_106,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_64,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_82,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k7_relset_1(A_76,B_77,C_78,D_79) = k9_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_85,plain,(
    ! [D_79] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_79) = k9_relat_1('#skF_8',D_79) ),
    inference(resolution,[status(thm)],[c_56,c_82])).

tff(c_46,plain,(
    ~ r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_86,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_46])).

tff(c_65,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_69,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_65])).

tff(c_52,plain,(
    r2_hidden('#skF_10','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_60,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,(
    k1_funct_1('#skF_8','#skF_10') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26,plain,(
    ! [A_43,B_46] :
      ( k1_funct_1(A_43,B_46) = k1_xboole_0
      | r2_hidden(B_46,k1_relat_1(A_43))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_96,plain,(
    ! [B_81,A_82] :
      ( r2_hidden(k4_tarski(B_81,k1_funct_1(A_82,B_81)),A_82)
      | ~ r2_hidden(B_81,k1_relat_1(A_82))
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_99,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_96])).

tff(c_101,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_60,c_99])).

tff(c_102,plain,(
    ~ r2_hidden('#skF_10',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_105,plain,
    ( k1_funct_1('#skF_8','#skF_10') = k1_xboole_0
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_102])).

tff(c_108,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_60,c_48,c_105])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_112,plain,(
    '#skF_6' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_54])).

tff(c_58,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_71,plain,(
    ! [A_69,B_70,C_71] :
      ( k1_relset_1(A_69,B_70,C_71) = k1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_75,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_71])).

tff(c_44,plain,(
    ! [B_59,A_58,C_60] :
      ( k1_xboole_0 = B_59
      | k1_relset_1(A_58,B_59,C_60) = A_58
      | ~ v1_funct_2(C_60,A_58,B_59)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_208,plain,(
    ! [B_111,A_112,C_113] :
      ( B_111 = '#skF_9'
      | k1_relset_1(A_112,B_111,C_113) = A_112
      | ~ v1_funct_2(C_113,A_112,B_111)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_112,B_111))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_44])).

tff(c_211,plain,
    ( '#skF_6' = '#skF_9'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_208])).

tff(c_214,plain,
    ( '#skF_6' = '#skF_9'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_75,c_211])).

tff(c_215,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_214])).

tff(c_216,plain,(
    ~ r2_hidden('#skF_10','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_102])).

tff(c_220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_216])).

tff(c_221,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_50,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_223,plain,(
    ! [D_114,A_115,B_116,E_117] :
      ( r2_hidden(D_114,k9_relat_1(A_115,B_116))
      | ~ r2_hidden(E_117,B_116)
      | ~ r2_hidden(k4_tarski(E_117,D_114),A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_242,plain,(
    ! [D_118,A_119] :
      ( r2_hidden(D_118,k9_relat_1(A_119,'#skF_7'))
      | ~ r2_hidden(k4_tarski('#skF_10',D_118),A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(resolution,[status(thm)],[c_50,c_223])).

tff(c_245,plain,
    ( r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_221,c_242])).

tff(c_256,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_245])).

tff(c_258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_256])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n014.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 12:16:37 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.33  
% 2.18/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.33  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.18/1.33  
% 2.18/1.33  %Foreground sorts:
% 2.18/1.33  
% 2.18/1.33  
% 2.18/1.33  %Background operators:
% 2.18/1.33  
% 2.18/1.33  
% 2.18/1.33  %Foreground operators:
% 2.18/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.18/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.18/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.18/1.33  tff('#skF_10', type, '#skF_10': $i).
% 2.18/1.33  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.18/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.18/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.18/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.18/1.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.18/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.18/1.33  tff('#skF_9', type, '#skF_9': $i).
% 2.18/1.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.18/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.18/1.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.18/1.33  tff('#skF_8', type, '#skF_8': $i).
% 2.18/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.18/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.33  
% 2.53/1.35  tff(f_106, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => (![E]: ((?[F]: ((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))) => r2_hidden(E, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_2)).
% 2.53/1.35  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.53/1.35  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.53/1.35  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 2.53/1.35  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.53/1.35  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.53/1.35  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 2.53/1.35  tff(c_56, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.53/1.35  tff(c_82, plain, (![A_76, B_77, C_78, D_79]: (k7_relset_1(A_76, B_77, C_78, D_79)=k9_relat_1(C_78, D_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.53/1.35  tff(c_85, plain, (![D_79]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_79)=k9_relat_1('#skF_8', D_79))), inference(resolution, [status(thm)], [c_56, c_82])).
% 2.53/1.35  tff(c_46, plain, (~r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.53/1.35  tff(c_86, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_46])).
% 2.53/1.35  tff(c_65, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.53/1.35  tff(c_69, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_65])).
% 2.53/1.35  tff(c_52, plain, (r2_hidden('#skF_10', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.53/1.35  tff(c_60, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.53/1.35  tff(c_48, plain, (k1_funct_1('#skF_8', '#skF_10')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.53/1.35  tff(c_26, plain, (![A_43, B_46]: (k1_funct_1(A_43, B_46)=k1_xboole_0 | r2_hidden(B_46, k1_relat_1(A_43)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.53/1.35  tff(c_96, plain, (![B_81, A_82]: (r2_hidden(k4_tarski(B_81, k1_funct_1(A_82, B_81)), A_82) | ~r2_hidden(B_81, k1_relat_1(A_82)) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.53/1.35  tff(c_99, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_48, c_96])).
% 2.53/1.35  tff(c_101, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_60, c_99])).
% 2.53/1.35  tff(c_102, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_101])).
% 2.53/1.35  tff(c_105, plain, (k1_funct_1('#skF_8', '#skF_10')=k1_xboole_0 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_26, c_102])).
% 2.53/1.35  tff(c_108, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_60, c_48, c_105])).
% 2.53/1.35  tff(c_54, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.53/1.35  tff(c_112, plain, ('#skF_6'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_54])).
% 2.53/1.35  tff(c_58, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.53/1.35  tff(c_71, plain, (![A_69, B_70, C_71]: (k1_relset_1(A_69, B_70, C_71)=k1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.53/1.35  tff(c_75, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_71])).
% 2.53/1.35  tff(c_44, plain, (![B_59, A_58, C_60]: (k1_xboole_0=B_59 | k1_relset_1(A_58, B_59, C_60)=A_58 | ~v1_funct_2(C_60, A_58, B_59) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.53/1.35  tff(c_208, plain, (![B_111, A_112, C_113]: (B_111='#skF_9' | k1_relset_1(A_112, B_111, C_113)=A_112 | ~v1_funct_2(C_113, A_112, B_111) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_112, B_111))))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_44])).
% 2.53/1.35  tff(c_211, plain, ('#skF_6'='#skF_9' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_208])).
% 2.53/1.35  tff(c_214, plain, ('#skF_6'='#skF_9' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_75, c_211])).
% 2.53/1.35  tff(c_215, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_112, c_214])).
% 2.53/1.35  tff(c_216, plain, (~r2_hidden('#skF_10', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_102])).
% 2.53/1.35  tff(c_220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_216])).
% 2.53/1.35  tff(c_221, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_101])).
% 2.53/1.35  tff(c_50, plain, (r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.53/1.35  tff(c_223, plain, (![D_114, A_115, B_116, E_117]: (r2_hidden(D_114, k9_relat_1(A_115, B_116)) | ~r2_hidden(E_117, B_116) | ~r2_hidden(k4_tarski(E_117, D_114), A_115) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.53/1.35  tff(c_242, plain, (![D_118, A_119]: (r2_hidden(D_118, k9_relat_1(A_119, '#skF_7')) | ~r2_hidden(k4_tarski('#skF_10', D_118), A_119) | ~v1_relat_1(A_119))), inference(resolution, [status(thm)], [c_50, c_223])).
% 2.53/1.35  tff(c_245, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_221, c_242])).
% 2.53/1.35  tff(c_256, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_245])).
% 2.53/1.35  tff(c_258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_256])).
% 2.53/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.35  
% 2.53/1.35  Inference rules
% 2.53/1.35  ----------------------
% 2.53/1.35  #Ref     : 0
% 2.53/1.35  #Sup     : 40
% 2.53/1.35  #Fact    : 0
% 2.53/1.35  #Define  : 0
% 2.53/1.35  #Split   : 1
% 2.53/1.35  #Chain   : 0
% 2.53/1.35  #Close   : 0
% 2.53/1.35  
% 2.53/1.35  Ordering : KBO
% 2.53/1.35  
% 2.53/1.35  Simplification rules
% 2.53/1.35  ----------------------
% 2.53/1.35  #Subsume      : 3
% 2.53/1.35  #Demod        : 42
% 2.53/1.35  #Tautology    : 11
% 2.53/1.35  #SimpNegUnit  : 4
% 2.53/1.35  #BackRed      : 7
% 2.53/1.35  
% 2.53/1.35  #Partial instantiations: 0
% 2.53/1.35  #Strategies tried      : 1
% 2.53/1.35  
% 2.53/1.35  Timing (in seconds)
% 2.53/1.35  ----------------------
% 2.53/1.35  Preprocessing        : 0.35
% 2.53/1.35  Parsing              : 0.18
% 2.53/1.35  CNF conversion       : 0.03
% 2.53/1.35  Main loop            : 0.21
% 2.53/1.35  Inferencing          : 0.07
% 2.53/1.35  Reduction            : 0.07
% 2.53/1.35  Demodulation         : 0.05
% 2.53/1.35  BG Simplification    : 0.02
% 2.53/1.35  Subsumption          : 0.04
% 2.53/1.35  Abstraction          : 0.01
% 2.53/1.35  MUC search           : 0.00
% 2.53/1.35  Cooper               : 0.00
% 2.53/1.35  Total                : 0.60
% 2.53/1.35  Index Insertion      : 0.00
% 2.53/1.35  Index Deletion       : 0.00
% 2.53/1.35  Index Matching       : 0.00
% 2.53/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
