%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:50 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 125 expanded)
%              Number of leaves         :   37 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :  119 ( 327 expanded)
%              Number of equality atoms :   28 (  68 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_12

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

tff('#skF_11',type,(
    '#skF_11': $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
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

tff(f_34,axiom,(
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
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_95,axiom,(
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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_51,axiom,(
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

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_60,plain,(
    r2_hidden('#skF_12','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_66,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_76,plain,(
    ! [B_77,A_78] :
      ( v1_relat_1(B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_78))
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_66,c_76])).

tff(c_82,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_79])).

tff(c_70,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_58,plain,(
    k1_funct_1('#skF_10','#skF_12') = '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_101,plain,(
    ! [A_93,C_94] :
      ( r2_hidden(k4_tarski(A_93,k1_funct_1(C_94,A_93)),C_94)
      | ~ r2_hidden(A_93,k1_relat_1(C_94))
      | ~ v1_funct_1(C_94)
      | ~ v1_relat_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_110,plain,
    ( r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10')
    | ~ r2_hidden('#skF_12',k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_101])).

tff(c_115,plain,
    ( r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10')
    | ~ r2_hidden('#skF_12',k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_70,c_110])).

tff(c_116,plain,(
    ~ r2_hidden('#skF_12',k1_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_68,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_119,plain,(
    ! [B_99,A_100,C_101] :
      ( k1_xboole_0 = B_99
      | k1_relset_1(A_100,B_99,C_101) = A_100
      | ~ v1_funct_2(C_101,A_100,B_99)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_122,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_119])).

tff(c_125,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_122])).

tff(c_126,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_125])).

tff(c_62,plain,(
    r2_hidden('#skF_12','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_176,plain,(
    ! [D_133,A_134,B_135,C_136] :
      ( r2_hidden(k4_tarski(D_133,'#skF_6'(A_134,B_135,C_136,D_133)),C_136)
      | ~ r2_hidden(D_133,B_135)
      | k1_relset_1(B_135,A_134,C_136) != B_135
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(B_135,A_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    ! [A_48,C_50,B_49] :
      ( r2_hidden(A_48,k1_relat_1(C_50))
      | ~ r2_hidden(k4_tarski(A_48,B_49),C_50)
      | ~ v1_funct_1(C_50)
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_191,plain,(
    ! [D_140,C_141,B_142,A_143] :
      ( r2_hidden(D_140,k1_relat_1(C_141))
      | ~ v1_funct_1(C_141)
      | ~ v1_relat_1(C_141)
      | ~ r2_hidden(D_140,B_142)
      | k1_relset_1(B_142,A_143,C_141) != B_142
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(B_142,A_143))) ) ),
    inference(resolution,[status(thm)],[c_176,c_34])).

tff(c_226,plain,(
    ! [C_146,A_147] :
      ( r2_hidden('#skF_12',k1_relat_1(C_146))
      | ~ v1_funct_1(C_146)
      | ~ v1_relat_1(C_146)
      | k1_relset_1('#skF_7',A_147,C_146) != '#skF_7'
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1('#skF_7',A_147))) ) ),
    inference(resolution,[status(thm)],[c_62,c_191])).

tff(c_229,plain,
    ( r2_hidden('#skF_12',k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10')
    | k1_relset_1('#skF_7','#skF_8','#skF_10') != '#skF_7' ),
    inference(resolution,[status(thm)],[c_66,c_226])).

tff(c_232,plain,(
    r2_hidden('#skF_12',k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_82,c_70,c_229])).

tff(c_234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_232])).

tff(c_236,plain,(
    r2_hidden('#skF_12',k1_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_276,plain,(
    ! [A_164,E_165,B_166] :
      ( r2_hidden(k1_funct_1(A_164,E_165),k9_relat_1(A_164,B_166))
      | ~ r2_hidden(E_165,B_166)
      | ~ r2_hidden(E_165,k1_relat_1(A_164))
      | ~ v1_funct_1(A_164)
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_279,plain,(
    ! [B_166] :
      ( r2_hidden('#skF_11',k9_relat_1('#skF_10',B_166))
      | ~ r2_hidden('#skF_12',B_166)
      | ~ r2_hidden('#skF_12',k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_276])).

tff(c_282,plain,(
    ! [B_167] :
      ( r2_hidden('#skF_11',k9_relat_1('#skF_10',B_167))
      | ~ r2_hidden('#skF_12',B_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_70,c_236,c_279])).

tff(c_86,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k7_relset_1(A_86,B_87,C_88,D_89) = k9_relat_1(C_88,D_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_89,plain,(
    ! [D_89] : k7_relset_1('#skF_7','#skF_8','#skF_10',D_89) = k9_relat_1('#skF_10',D_89) ),
    inference(resolution,[status(thm)],[c_66,c_86])).

tff(c_56,plain,(
    ~ r2_hidden('#skF_11',k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_91,plain,(
    ~ r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_56])).

tff(c_285,plain,(
    ~ r2_hidden('#skF_12','#skF_9') ),
    inference(resolution,[status(thm)],[c_282,c_91])).

tff(c_289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_285])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.34  
% 2.62/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.34  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_12
% 2.62/1.34  
% 2.62/1.34  %Foreground sorts:
% 2.62/1.34  
% 2.62/1.34  
% 2.62/1.34  %Background operators:
% 2.62/1.34  
% 2.62/1.34  
% 2.62/1.34  %Foreground operators:
% 2.62/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.62/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.34  tff('#skF_11', type, '#skF_11': $i).
% 2.62/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.62/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.62/1.34  tff('#skF_10', type, '#skF_10': $i).
% 2.62/1.34  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.62/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.62/1.34  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.62/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.62/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.62/1.34  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.62/1.34  tff('#skF_9', type, '#skF_9': $i).
% 2.62/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.62/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.62/1.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.62/1.34  tff('#skF_8', type, '#skF_8': $i).
% 2.62/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.62/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.34  tff('#skF_12', type, '#skF_12': $i).
% 2.62/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.34  
% 2.62/1.36  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => (![E]: ((?[F]: ((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))) => r2_hidden(E, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_2)).
% 2.62/1.36  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.62/1.36  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.62/1.36  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.62/1.36  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.62/1.36  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 2.62/1.36  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 2.62/1.36  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.62/1.36  tff(c_60, plain, (r2_hidden('#skF_12', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.62/1.36  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.62/1.36  tff(c_66, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.62/1.36  tff(c_76, plain, (![B_77, A_78]: (v1_relat_1(B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_78)) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.62/1.36  tff(c_79, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_66, c_76])).
% 2.62/1.36  tff(c_82, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_79])).
% 2.62/1.36  tff(c_70, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.62/1.36  tff(c_58, plain, (k1_funct_1('#skF_10', '#skF_12')='#skF_11'), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.62/1.36  tff(c_101, plain, (![A_93, C_94]: (r2_hidden(k4_tarski(A_93, k1_funct_1(C_94, A_93)), C_94) | ~r2_hidden(A_93, k1_relat_1(C_94)) | ~v1_funct_1(C_94) | ~v1_relat_1(C_94))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.62/1.36  tff(c_110, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10') | ~r2_hidden('#skF_12', k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_58, c_101])).
% 2.62/1.36  tff(c_115, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10') | ~r2_hidden('#skF_12', k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_70, c_110])).
% 2.62/1.36  tff(c_116, plain, (~r2_hidden('#skF_12', k1_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_115])).
% 2.62/1.36  tff(c_64, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.62/1.36  tff(c_68, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.62/1.36  tff(c_119, plain, (![B_99, A_100, C_101]: (k1_xboole_0=B_99 | k1_relset_1(A_100, B_99, C_101)=A_100 | ~v1_funct_2(C_101, A_100, B_99) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.62/1.36  tff(c_122, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_66, c_119])).
% 2.62/1.36  tff(c_125, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_122])).
% 2.62/1.36  tff(c_126, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_64, c_125])).
% 2.62/1.36  tff(c_62, plain, (r2_hidden('#skF_12', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.62/1.36  tff(c_176, plain, (![D_133, A_134, B_135, C_136]: (r2_hidden(k4_tarski(D_133, '#skF_6'(A_134, B_135, C_136, D_133)), C_136) | ~r2_hidden(D_133, B_135) | k1_relset_1(B_135, A_134, C_136)!=B_135 | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(B_135, A_134))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.62/1.36  tff(c_34, plain, (![A_48, C_50, B_49]: (r2_hidden(A_48, k1_relat_1(C_50)) | ~r2_hidden(k4_tarski(A_48, B_49), C_50) | ~v1_funct_1(C_50) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.62/1.36  tff(c_191, plain, (![D_140, C_141, B_142, A_143]: (r2_hidden(D_140, k1_relat_1(C_141)) | ~v1_funct_1(C_141) | ~v1_relat_1(C_141) | ~r2_hidden(D_140, B_142) | k1_relset_1(B_142, A_143, C_141)!=B_142 | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(B_142, A_143))))), inference(resolution, [status(thm)], [c_176, c_34])).
% 2.62/1.36  tff(c_226, plain, (![C_146, A_147]: (r2_hidden('#skF_12', k1_relat_1(C_146)) | ~v1_funct_1(C_146) | ~v1_relat_1(C_146) | k1_relset_1('#skF_7', A_147, C_146)!='#skF_7' | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1('#skF_7', A_147))))), inference(resolution, [status(thm)], [c_62, c_191])).
% 2.62/1.36  tff(c_229, plain, (r2_hidden('#skF_12', k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | k1_relset_1('#skF_7', '#skF_8', '#skF_10')!='#skF_7'), inference(resolution, [status(thm)], [c_66, c_226])).
% 2.62/1.36  tff(c_232, plain, (r2_hidden('#skF_12', k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_82, c_70, c_229])).
% 2.62/1.36  tff(c_234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_232])).
% 2.62/1.36  tff(c_236, plain, (r2_hidden('#skF_12', k1_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_115])).
% 2.62/1.36  tff(c_276, plain, (![A_164, E_165, B_166]: (r2_hidden(k1_funct_1(A_164, E_165), k9_relat_1(A_164, B_166)) | ~r2_hidden(E_165, B_166) | ~r2_hidden(E_165, k1_relat_1(A_164)) | ~v1_funct_1(A_164) | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.62/1.36  tff(c_279, plain, (![B_166]: (r2_hidden('#skF_11', k9_relat_1('#skF_10', B_166)) | ~r2_hidden('#skF_12', B_166) | ~r2_hidden('#skF_12', k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_276])).
% 2.62/1.36  tff(c_282, plain, (![B_167]: (r2_hidden('#skF_11', k9_relat_1('#skF_10', B_167)) | ~r2_hidden('#skF_12', B_167))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_70, c_236, c_279])).
% 2.62/1.36  tff(c_86, plain, (![A_86, B_87, C_88, D_89]: (k7_relset_1(A_86, B_87, C_88, D_89)=k9_relat_1(C_88, D_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.62/1.36  tff(c_89, plain, (![D_89]: (k7_relset_1('#skF_7', '#skF_8', '#skF_10', D_89)=k9_relat_1('#skF_10', D_89))), inference(resolution, [status(thm)], [c_66, c_86])).
% 2.62/1.36  tff(c_56, plain, (~r2_hidden('#skF_11', k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.62/1.36  tff(c_91, plain, (~r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_56])).
% 2.62/1.36  tff(c_285, plain, (~r2_hidden('#skF_12', '#skF_9')), inference(resolution, [status(thm)], [c_282, c_91])).
% 2.62/1.36  tff(c_289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_285])).
% 2.62/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.36  
% 2.62/1.36  Inference rules
% 2.62/1.36  ----------------------
% 2.62/1.36  #Ref     : 0
% 2.62/1.36  #Sup     : 44
% 2.62/1.36  #Fact    : 0
% 2.62/1.36  #Define  : 0
% 2.62/1.36  #Split   : 1
% 2.62/1.36  #Chain   : 0
% 2.62/1.36  #Close   : 0
% 2.62/1.36  
% 2.62/1.36  Ordering : KBO
% 2.62/1.36  
% 2.62/1.36  Simplification rules
% 2.62/1.36  ----------------------
% 2.62/1.36  #Subsume      : 1
% 2.62/1.36  #Demod        : 26
% 2.62/1.36  #Tautology    : 18
% 2.62/1.36  #SimpNegUnit  : 5
% 2.62/1.36  #BackRed      : 1
% 2.62/1.36  
% 2.62/1.36  #Partial instantiations: 0
% 2.62/1.36  #Strategies tried      : 1
% 2.62/1.36  
% 2.62/1.36  Timing (in seconds)
% 2.62/1.36  ----------------------
% 2.62/1.36  Preprocessing        : 0.34
% 2.62/1.36  Parsing              : 0.17
% 2.62/1.36  CNF conversion       : 0.03
% 2.62/1.36  Main loop            : 0.24
% 2.62/1.36  Inferencing          : 0.09
% 2.62/1.36  Reduction            : 0.07
% 2.62/1.36  Demodulation         : 0.05
% 2.62/1.36  BG Simplification    : 0.02
% 2.62/1.36  Subsumption          : 0.04
% 2.62/1.36  Abstraction          : 0.01
% 2.62/1.36  MUC search           : 0.00
% 2.62/1.36  Cooper               : 0.00
% 2.62/1.36  Total                : 0.62
% 2.62/1.36  Index Insertion      : 0.00
% 2.62/1.36  Index Deletion       : 0.00
% 2.62/1.36  Index Matching       : 0.00
% 2.62/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
