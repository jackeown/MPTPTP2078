%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:33 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 120 expanded)
%              Number of leaves         :   37 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  123 ( 294 expanded)
%              Number of equality atoms :   29 (  64 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_94,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_75,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_79,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_75])).

tff(c_62,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_391,plain,(
    ! [A_155,B_156,D_157] :
      ( k1_funct_1(A_155,'#skF_4'(A_155,B_156,k9_relat_1(A_155,B_156),D_157)) = D_157
      | ~ r2_hidden(D_157,k9_relat_1(A_155,B_156))
      | ~ v1_funct_1(A_155)
      | ~ v1_relat_1(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_60,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_86,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_relset_1(A_88,B_89,C_90) = k1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_90,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_86])).

tff(c_194,plain,(
    ! [B_114,A_115,C_116] :
      ( k1_xboole_0 = B_114
      | k1_relset_1(A_115,B_114,C_116) = A_115
      | ~ v1_funct_2(C_116,A_115,B_114)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_201,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_194])).

tff(c_205,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_90,c_201])).

tff(c_206,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_318,plain,(
    ! [A_134,B_135,D_136] :
      ( r2_hidden('#skF_4'(A_134,B_135,k9_relat_1(A_134,B_135),D_136),k1_relat_1(A_134))
      | ~ r2_hidden(D_136,k9_relat_1(A_134,B_135))
      | ~ v1_funct_1(A_134)
      | ~ v1_relat_1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_329,plain,(
    ! [B_135,D_136] :
      ( r2_hidden('#skF_4'('#skF_8',B_135,k9_relat_1('#skF_8',B_135),D_136),'#skF_5')
      | ~ r2_hidden(D_136,k9_relat_1('#skF_8',B_135))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_318])).

tff(c_356,plain,(
    ! [B_140,D_141] :
      ( r2_hidden('#skF_4'('#skF_8',B_140,k9_relat_1('#skF_8',B_140),D_141),'#skF_5')
      | ~ r2_hidden(D_141,k9_relat_1('#skF_8',B_140)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_62,c_329])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_369,plain,(
    ! [B_144,D_145] :
      ( m1_subset_1('#skF_4'('#skF_8',B_144,k9_relat_1('#skF_8',B_144),D_145),'#skF_5')
      | ~ r2_hidden(D_145,k9_relat_1('#skF_8',B_144)) ) ),
    inference(resolution,[status(thm)],[c_356,c_6])).

tff(c_228,plain,(
    ! [A_120,B_121,D_122] :
      ( r2_hidden('#skF_4'(A_120,B_121,k9_relat_1(A_120,B_121),D_122),B_121)
      | ~ r2_hidden(D_122,k9_relat_1(A_120,B_121))
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_54,plain,(
    ! [F_73] :
      ( k1_funct_1('#skF_8',F_73) != '#skF_9'
      | ~ r2_hidden(F_73,'#skF_7')
      | ~ m1_subset_1(F_73,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_242,plain,(
    ! [A_120,D_122] :
      ( k1_funct_1('#skF_8','#skF_4'(A_120,'#skF_7',k9_relat_1(A_120,'#skF_7'),D_122)) != '#skF_9'
      | ~ m1_subset_1('#skF_4'(A_120,'#skF_7',k9_relat_1(A_120,'#skF_7'),D_122),'#skF_5')
      | ~ r2_hidden(D_122,k9_relat_1(A_120,'#skF_7'))
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(resolution,[status(thm)],[c_228,c_54])).

tff(c_373,plain,(
    ! [D_145] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_145)) != '#skF_9'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_145,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_369,c_242])).

tff(c_376,plain,(
    ! [D_145] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_145)) != '#skF_9'
      | ~ r2_hidden(D_145,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_62,c_373])).

tff(c_401,plain,(
    ! [D_157] :
      ( D_157 != '#skF_9'
      | ~ r2_hidden(D_157,k9_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_157,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_376])).

tff(c_412,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_62,c_401])).

tff(c_131,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( k7_relset_1(A_98,B_99,C_100,D_101) = k9_relat_1(C_100,D_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_138,plain,(
    ! [D_101] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_101) = k9_relat_1('#skF_8',D_101) ),
    inference(resolution,[status(thm)],[c_58,c_131])).

tff(c_56,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_142,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_56])).

tff(c_414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_412,c_142])).

tff(c_415,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_422,plain,(
    ! [A_1] : r1_tarski('#skF_6',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_2])).

tff(c_96,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( m1_subset_1(k7_relset_1(A_93,B_94,C_95,D_96),k1_zfmisc_1(B_94))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_80,plain,(
    ! [C_83,A_84,B_85] :
      ( r2_hidden(C_83,A_84)
      | ~ r2_hidden(C_83,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_83,plain,(
    ! [A_84] :
      ( r2_hidden('#skF_9',A_84)
      | ~ m1_subset_1(k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7'),k1_zfmisc_1(A_84)) ) ),
    inference(resolution,[status(thm)],[c_56,c_80])).

tff(c_108,plain,
    ( r2_hidden('#skF_9','#skF_6')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_96,c_83])).

tff(c_117,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_108])).

tff(c_32,plain,(
    ! [B_51,A_50] :
      ( ~ r1_tarski(B_51,A_50)
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_129,plain,(
    ~ r1_tarski('#skF_6','#skF_9') ),
    inference(resolution,[status(thm)],[c_117,c_32])).

tff(c_441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n019.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 12:03:22 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.35  
% 2.62/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.35  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.62/1.35  
% 2.62/1.35  %Foreground sorts:
% 2.62/1.35  
% 2.62/1.35  
% 2.62/1.35  %Background operators:
% 2.62/1.35  
% 2.62/1.35  
% 2.62/1.35  %Foreground operators:
% 2.62/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.62/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.62/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.35  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.62/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.62/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.62/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.62/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.62/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.62/1.35  tff('#skF_9', type, '#skF_9': $i).
% 2.62/1.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.62/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.62/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.62/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.62/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.62/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.35  
% 2.62/1.37  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 2.62/1.37  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.62/1.37  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 2.62/1.37  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.62/1.37  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.62/1.37  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.62/1.37  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.62/1.37  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.62/1.37  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 2.62/1.37  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.62/1.37  tff(f_60, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.62/1.37  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.62/1.37  tff(c_75, plain, (![C_80, A_81, B_82]: (v1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.62/1.37  tff(c_79, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_75])).
% 2.62/1.37  tff(c_62, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.62/1.37  tff(c_391, plain, (![A_155, B_156, D_157]: (k1_funct_1(A_155, '#skF_4'(A_155, B_156, k9_relat_1(A_155, B_156), D_157))=D_157 | ~r2_hidden(D_157, k9_relat_1(A_155, B_156)) | ~v1_funct_1(A_155) | ~v1_relat_1(A_155))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.62/1.37  tff(c_60, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.62/1.37  tff(c_86, plain, (![A_88, B_89, C_90]: (k1_relset_1(A_88, B_89, C_90)=k1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.62/1.37  tff(c_90, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_86])).
% 2.62/1.37  tff(c_194, plain, (![B_114, A_115, C_116]: (k1_xboole_0=B_114 | k1_relset_1(A_115, B_114, C_116)=A_115 | ~v1_funct_2(C_116, A_115, B_114) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.62/1.37  tff(c_201, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_194])).
% 2.62/1.37  tff(c_205, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_90, c_201])).
% 2.62/1.37  tff(c_206, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_205])).
% 2.62/1.37  tff(c_318, plain, (![A_134, B_135, D_136]: (r2_hidden('#skF_4'(A_134, B_135, k9_relat_1(A_134, B_135), D_136), k1_relat_1(A_134)) | ~r2_hidden(D_136, k9_relat_1(A_134, B_135)) | ~v1_funct_1(A_134) | ~v1_relat_1(A_134))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.62/1.37  tff(c_329, plain, (![B_135, D_136]: (r2_hidden('#skF_4'('#skF_8', B_135, k9_relat_1('#skF_8', B_135), D_136), '#skF_5') | ~r2_hidden(D_136, k9_relat_1('#skF_8', B_135)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_206, c_318])).
% 2.62/1.37  tff(c_356, plain, (![B_140, D_141]: (r2_hidden('#skF_4'('#skF_8', B_140, k9_relat_1('#skF_8', B_140), D_141), '#skF_5') | ~r2_hidden(D_141, k9_relat_1('#skF_8', B_140)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_62, c_329])).
% 2.62/1.37  tff(c_6, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.62/1.37  tff(c_369, plain, (![B_144, D_145]: (m1_subset_1('#skF_4'('#skF_8', B_144, k9_relat_1('#skF_8', B_144), D_145), '#skF_5') | ~r2_hidden(D_145, k9_relat_1('#skF_8', B_144)))), inference(resolution, [status(thm)], [c_356, c_6])).
% 2.62/1.37  tff(c_228, plain, (![A_120, B_121, D_122]: (r2_hidden('#skF_4'(A_120, B_121, k9_relat_1(A_120, B_121), D_122), B_121) | ~r2_hidden(D_122, k9_relat_1(A_120, B_121)) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.62/1.37  tff(c_54, plain, (![F_73]: (k1_funct_1('#skF_8', F_73)!='#skF_9' | ~r2_hidden(F_73, '#skF_7') | ~m1_subset_1(F_73, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.62/1.37  tff(c_242, plain, (![A_120, D_122]: (k1_funct_1('#skF_8', '#skF_4'(A_120, '#skF_7', k9_relat_1(A_120, '#skF_7'), D_122))!='#skF_9' | ~m1_subset_1('#skF_4'(A_120, '#skF_7', k9_relat_1(A_120, '#skF_7'), D_122), '#skF_5') | ~r2_hidden(D_122, k9_relat_1(A_120, '#skF_7')) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(resolution, [status(thm)], [c_228, c_54])).
% 2.62/1.37  tff(c_373, plain, (![D_145]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_145))!='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_145, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_369, c_242])).
% 2.62/1.37  tff(c_376, plain, (![D_145]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_145))!='#skF_9' | ~r2_hidden(D_145, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_62, c_373])).
% 2.62/1.37  tff(c_401, plain, (![D_157]: (D_157!='#skF_9' | ~r2_hidden(D_157, k9_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(D_157, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_391, c_376])).
% 2.62/1.37  tff(c_412, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_62, c_401])).
% 2.62/1.37  tff(c_131, plain, (![A_98, B_99, C_100, D_101]: (k7_relset_1(A_98, B_99, C_100, D_101)=k9_relat_1(C_100, D_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.62/1.37  tff(c_138, plain, (![D_101]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_101)=k9_relat_1('#skF_8', D_101))), inference(resolution, [status(thm)], [c_58, c_131])).
% 2.62/1.37  tff(c_56, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.62/1.37  tff(c_142, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_56])).
% 2.62/1.37  tff(c_414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_412, c_142])).
% 2.62/1.37  tff(c_415, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_205])).
% 2.62/1.37  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.62/1.37  tff(c_422, plain, (![A_1]: (r1_tarski('#skF_6', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_415, c_2])).
% 2.62/1.37  tff(c_96, plain, (![A_93, B_94, C_95, D_96]: (m1_subset_1(k7_relset_1(A_93, B_94, C_95, D_96), k1_zfmisc_1(B_94)) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.62/1.37  tff(c_80, plain, (![C_83, A_84, B_85]: (r2_hidden(C_83, A_84) | ~r2_hidden(C_83, B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.62/1.37  tff(c_83, plain, (![A_84]: (r2_hidden('#skF_9', A_84) | ~m1_subset_1(k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'), k1_zfmisc_1(A_84)))), inference(resolution, [status(thm)], [c_56, c_80])).
% 2.62/1.37  tff(c_108, plain, (r2_hidden('#skF_9', '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_96, c_83])).
% 2.62/1.37  tff(c_117, plain, (r2_hidden('#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_108])).
% 2.62/1.37  tff(c_32, plain, (![B_51, A_50]: (~r1_tarski(B_51, A_50) | ~r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.62/1.37  tff(c_129, plain, (~r1_tarski('#skF_6', '#skF_9')), inference(resolution, [status(thm)], [c_117, c_32])).
% 2.62/1.37  tff(c_441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_422, c_129])).
% 2.62/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.37  
% 2.62/1.37  Inference rules
% 2.62/1.37  ----------------------
% 2.62/1.37  #Ref     : 0
% 2.62/1.37  #Sup     : 76
% 2.62/1.37  #Fact    : 0
% 2.62/1.37  #Define  : 0
% 2.62/1.37  #Split   : 1
% 2.62/1.37  #Chain   : 0
% 2.62/1.37  #Close   : 0
% 2.62/1.37  
% 2.62/1.37  Ordering : KBO
% 2.62/1.37  
% 2.62/1.37  Simplification rules
% 2.62/1.37  ----------------------
% 2.62/1.37  #Subsume      : 5
% 2.62/1.37  #Demod        : 44
% 2.62/1.37  #Tautology    : 15
% 2.62/1.37  #SimpNegUnit  : 1
% 2.62/1.37  #BackRed      : 13
% 2.62/1.37  
% 2.62/1.37  #Partial instantiations: 0
% 2.62/1.37  #Strategies tried      : 1
% 2.62/1.37  
% 2.62/1.37  Timing (in seconds)
% 2.62/1.37  ----------------------
% 2.62/1.37  Preprocessing        : 0.33
% 2.62/1.37  Parsing              : 0.16
% 2.62/1.37  CNF conversion       : 0.03
% 2.62/1.37  Main loop            : 0.28
% 2.62/1.37  Inferencing          : 0.10
% 2.62/1.37  Reduction            : 0.08
% 2.62/1.37  Demodulation         : 0.06
% 2.62/1.37  BG Simplification    : 0.02
% 2.62/1.37  Subsumption          : 0.05
% 2.62/1.37  Abstraction          : 0.02
% 2.62/1.37  MUC search           : 0.00
% 2.62/1.37  Cooper               : 0.00
% 2.62/1.37  Total                : 0.65
% 2.62/1.37  Index Insertion      : 0.00
% 2.62/1.37  Index Deletion       : 0.00
% 2.62/1.37  Index Matching       : 0.00
% 2.62/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
