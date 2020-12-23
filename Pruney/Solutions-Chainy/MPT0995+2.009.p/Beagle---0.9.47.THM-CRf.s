%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:50 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 173 expanded)
%              Number of leaves         :   35 (  78 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 481 expanded)
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

tff(f_111,negated_conjecture,(
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

tff(f_73,axiom,(
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

tff(f_65,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
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

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_86,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( k7_relset_1(A_77,B_78,C_79,D_80) = k9_relat_1(C_79,D_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_89,plain,(
    ! [D_80] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_80) = k9_relat_1('#skF_8',D_80) ),
    inference(resolution,[status(thm)],[c_58,c_86])).

tff(c_48,plain,(
    ~ r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_90,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_48])).

tff(c_22,plain,(
    ! [A_46,B_47] : v1_relat_1(k2_zfmisc_1(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_68,plain,(
    ! [B_69,A_70] :
      ( v1_relat_1(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_58,c_68])).

tff(c_74,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_71])).

tff(c_54,plain,(
    r2_hidden('#skF_10','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_62,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_50,plain,(
    k1_funct_1('#skF_8','#skF_10') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    ! [A_48,B_51] :
      ( k1_funct_1(A_48,B_51) = k1_xboole_0
      | r2_hidden(B_51,k1_relat_1(A_48))
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_125,plain,(
    ! [B_96,A_97] :
      ( r2_hidden(k4_tarski(B_96,k1_funct_1(A_97,B_96)),A_97)
      | ~ r2_hidden(B_96,k1_relat_1(A_97))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_138,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_125])).

tff(c_143,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_62,c_138])).

tff(c_148,plain,(
    ~ r2_hidden('#skF_10',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_151,plain,
    ( k1_funct_1('#skF_8','#skF_10') = k1_xboole_0
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_30,c_148])).

tff(c_154,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_62,c_50,c_151])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_160,plain,(
    '#skF_6' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_56])).

tff(c_60,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_76,plain,(
    ! [A_72,B_73,C_74] :
      ( k1_relset_1(A_72,B_73,C_74) = k1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_80,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_76])).

tff(c_46,plain,(
    ! [B_61,A_60,C_62] :
      ( k1_xboole_0 = B_61
      | k1_relset_1(A_60,B_61,C_62) = A_60
      | ~ v1_funct_2(C_62,A_60,B_61)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_207,plain,(
    ! [B_108,A_109,C_110] :
      ( B_108 = '#skF_9'
      | k1_relset_1(A_109,B_108,C_110) = A_109
      | ~ v1_funct_2(C_110,A_109,B_108)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_46])).

tff(c_210,plain,
    ( '#skF_6' = '#skF_9'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_207])).

tff(c_213,plain,
    ( '#skF_6' = '#skF_9'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_80,c_210])).

tff(c_214,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_213])).

tff(c_215,plain,(
    ~ r2_hidden('#skF_10','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_148])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_215])).

tff(c_220,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_52,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_101,plain,(
    ! [D_84,A_85,B_86,E_87] :
      ( r2_hidden(D_84,k9_relat_1(A_85,B_86))
      | ~ r2_hidden(E_87,B_86)
      | ~ r2_hidden(k4_tarski(E_87,D_84),A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_109,plain,(
    ! [D_84,A_85] :
      ( r2_hidden(D_84,k9_relat_1(A_85,'#skF_7'))
      | ~ r2_hidden(k4_tarski('#skF_10',D_84),A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(resolution,[status(thm)],[c_52,c_101])).

tff(c_230,plain,
    ( r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_220,c_109])).

tff(c_238,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_230])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:30:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.29  
% 2.13/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.29  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.13/1.29  
% 2.13/1.29  %Foreground sorts:
% 2.13/1.29  
% 2.13/1.29  
% 2.13/1.29  %Background operators:
% 2.13/1.29  
% 2.13/1.29  
% 2.13/1.29  %Foreground operators:
% 2.13/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.13/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.13/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.29  tff('#skF_7', type, '#skF_7': $i).
% 2.13/1.29  tff('#skF_10', type, '#skF_10': $i).
% 2.13/1.29  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.13/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.13/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.13/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.13/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.13/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.13/1.29  tff('#skF_9', type, '#skF_9': $i).
% 2.13/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.13/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.13/1.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.13/1.29  tff('#skF_8', type, '#skF_8': $i).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.13/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.29  
% 2.40/1.30  tff(f_111, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => (![E]: ((?[F]: ((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))) => r2_hidden(E, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_2)).
% 2.40/1.30  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.40/1.30  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.40/1.30  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.40/1.30  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 2.40/1.30  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.40/1.30  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.40/1.30  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 2.40/1.30  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.40/1.30  tff(c_86, plain, (![A_77, B_78, C_79, D_80]: (k7_relset_1(A_77, B_78, C_79, D_80)=k9_relat_1(C_79, D_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.40/1.30  tff(c_89, plain, (![D_80]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_80)=k9_relat_1('#skF_8', D_80))), inference(resolution, [status(thm)], [c_58, c_86])).
% 2.40/1.30  tff(c_48, plain, (~r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.40/1.30  tff(c_90, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_48])).
% 2.40/1.30  tff(c_22, plain, (![A_46, B_47]: (v1_relat_1(k2_zfmisc_1(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.40/1.30  tff(c_68, plain, (![B_69, A_70]: (v1_relat_1(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.40/1.30  tff(c_71, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_68])).
% 2.40/1.30  tff(c_74, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_71])).
% 2.40/1.30  tff(c_54, plain, (r2_hidden('#skF_10', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.40/1.30  tff(c_62, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.40/1.30  tff(c_50, plain, (k1_funct_1('#skF_8', '#skF_10')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.40/1.30  tff(c_30, plain, (![A_48, B_51]: (k1_funct_1(A_48, B_51)=k1_xboole_0 | r2_hidden(B_51, k1_relat_1(A_48)) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.40/1.30  tff(c_125, plain, (![B_96, A_97]: (r2_hidden(k4_tarski(B_96, k1_funct_1(A_97, B_96)), A_97) | ~r2_hidden(B_96, k1_relat_1(A_97)) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.40/1.30  tff(c_138, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_50, c_125])).
% 2.40/1.30  tff(c_143, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_62, c_138])).
% 2.40/1.30  tff(c_148, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_143])).
% 2.40/1.30  tff(c_151, plain, (k1_funct_1('#skF_8', '#skF_10')=k1_xboole_0 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_30, c_148])).
% 2.40/1.30  tff(c_154, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_62, c_50, c_151])).
% 2.40/1.30  tff(c_56, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.40/1.30  tff(c_160, plain, ('#skF_6'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_56])).
% 2.40/1.30  tff(c_60, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.40/1.30  tff(c_76, plain, (![A_72, B_73, C_74]: (k1_relset_1(A_72, B_73, C_74)=k1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.40/1.30  tff(c_80, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_76])).
% 2.40/1.30  tff(c_46, plain, (![B_61, A_60, C_62]: (k1_xboole_0=B_61 | k1_relset_1(A_60, B_61, C_62)=A_60 | ~v1_funct_2(C_62, A_60, B_61) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.40/1.30  tff(c_207, plain, (![B_108, A_109, C_110]: (B_108='#skF_9' | k1_relset_1(A_109, B_108, C_110)=A_109 | ~v1_funct_2(C_110, A_109, B_108) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_46])).
% 2.40/1.30  tff(c_210, plain, ('#skF_6'='#skF_9' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_207])).
% 2.40/1.30  tff(c_213, plain, ('#skF_6'='#skF_9' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_80, c_210])).
% 2.40/1.30  tff(c_214, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_160, c_213])).
% 2.40/1.30  tff(c_215, plain, (~r2_hidden('#skF_10', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_214, c_148])).
% 2.40/1.30  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_215])).
% 2.40/1.30  tff(c_220, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_143])).
% 2.40/1.30  tff(c_52, plain, (r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.40/1.30  tff(c_101, plain, (![D_84, A_85, B_86, E_87]: (r2_hidden(D_84, k9_relat_1(A_85, B_86)) | ~r2_hidden(E_87, B_86) | ~r2_hidden(k4_tarski(E_87, D_84), A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.40/1.30  tff(c_109, plain, (![D_84, A_85]: (r2_hidden(D_84, k9_relat_1(A_85, '#skF_7')) | ~r2_hidden(k4_tarski('#skF_10', D_84), A_85) | ~v1_relat_1(A_85))), inference(resolution, [status(thm)], [c_52, c_101])).
% 2.40/1.30  tff(c_230, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_220, c_109])).
% 2.40/1.30  tff(c_238, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_230])).
% 2.40/1.30  tff(c_240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_238])).
% 2.40/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.30  
% 2.40/1.30  Inference rules
% 2.40/1.30  ----------------------
% 2.40/1.30  #Ref     : 0
% 2.40/1.30  #Sup     : 35
% 2.40/1.30  #Fact    : 0
% 2.40/1.30  #Define  : 0
% 2.40/1.30  #Split   : 1
% 2.40/1.30  #Chain   : 0
% 2.40/1.30  #Close   : 0
% 2.40/1.30  
% 2.40/1.30  Ordering : KBO
% 2.40/1.30  
% 2.40/1.30  Simplification rules
% 2.40/1.30  ----------------------
% 2.40/1.30  #Subsume      : 3
% 2.40/1.30  #Demod        : 41
% 2.40/1.30  #Tautology    : 9
% 2.40/1.31  #SimpNegUnit  : 3
% 2.40/1.31  #BackRed      : 9
% 2.40/1.31  
% 2.40/1.31  #Partial instantiations: 0
% 2.40/1.31  #Strategies tried      : 1
% 2.40/1.31  
% 2.40/1.31  Timing (in seconds)
% 2.40/1.31  ----------------------
% 2.40/1.31  Preprocessing        : 0.34
% 2.40/1.31  Parsing              : 0.17
% 2.40/1.31  CNF conversion       : 0.03
% 2.40/1.31  Main loop            : 0.19
% 2.40/1.31  Inferencing          : 0.06
% 2.40/1.31  Reduction            : 0.06
% 2.40/1.31  Demodulation         : 0.04
% 2.40/1.31  BG Simplification    : 0.02
% 2.40/1.31  Subsumption          : 0.03
% 2.40/1.31  Abstraction          : 0.02
% 2.40/1.31  MUC search           : 0.00
% 2.40/1.31  Cooper               : 0.00
% 2.40/1.31  Total                : 0.57
% 2.40/1.31  Index Insertion      : 0.00
% 2.40/1.31  Index Deletion       : 0.00
% 2.40/1.31  Index Matching       : 0.00
% 2.40/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
