%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:19 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 173 expanded)
%              Number of leaves         :   39 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  135 ( 443 expanded)
%              Number of equality atoms :   38 ( 126 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
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

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_161,plain,(
    ! [A_104,B_105,C_106] :
      ( k2_relset_1(A_104,B_105,C_106) = k2_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_165,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_161])).

tff(c_60,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_167,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_60])).

tff(c_105,plain,(
    ! [C_81,A_82,B_83] :
      ( v1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_109,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_105])).

tff(c_147,plain,(
    ! [C_98,B_99,A_100] :
      ( v5_relat_1(C_98,B_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_151,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_147])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_172,plain,(
    ! [A_108,B_109,C_110] :
      ( k1_relset_1(A_108,B_109,C_110) = k1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_176,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_172])).

tff(c_248,plain,(
    ! [B_138,A_139,C_140] :
      ( k1_xboole_0 = B_138
      | k1_relset_1(A_139,B_138,C_140) = A_139
      | ~ v1_funct_2(C_140,A_139,B_138)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_251,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_248])).

tff(c_254,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_176,c_251])).

tff(c_261,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_70,plain,(
    ! [D_69] :
      ( r2_hidden('#skF_9'(D_69),'#skF_6')
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_125,plain,(
    ! [C_90,B_91,A_92] :
      ( r2_hidden(C_90,B_91)
      | ~ r2_hidden(C_90,A_92)
      | ~ r1_tarski(A_92,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_131,plain,(
    ! [D_69,B_91] :
      ( r2_hidden('#skF_9'(D_69),B_91)
      | ~ r1_tarski('#skF_6',B_91)
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_125])).

tff(c_66,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_68,plain,(
    ! [D_69] :
      ( k1_funct_1('#skF_8','#skF_9'(D_69)) = D_69
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_200,plain,(
    ! [A_116,D_117] :
      ( r2_hidden(k1_funct_1(A_116,D_117),k2_relat_1(A_116))
      | ~ r2_hidden(D_117,k1_relat_1(A_116))
      | ~ v1_funct_1(A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_205,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_69),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_200])).

tff(c_209,plain,(
    ! [D_118] :
      ( r2_hidden(D_118,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_118),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_118,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_66,c_205])).

tff(c_214,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_69,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_131,c_209])).

tff(c_215,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_262,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_215])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_262])).

tff(c_268,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_115,plain,(
    ! [B_87,A_88] :
      ( r1_tarski(k2_relat_1(B_87),A_88)
      | ~ v5_relat_1(B_87,A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_123,plain,(
    ! [B_87] :
      ( k2_relat_1(B_87) = k1_xboole_0
      | ~ v5_relat_1(B_87,k1_xboole_0)
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_115,c_14])).

tff(c_294,plain,(
    ! [B_145] :
      ( k2_relat_1(B_145) = '#skF_7'
      | ~ v5_relat_1(B_145,'#skF_7')
      | ~ v1_relat_1(B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_268,c_123])).

tff(c_297,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_151,c_294])).

tff(c_300,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_297])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_300])).

tff(c_313,plain,(
    ! [D_146] :
      ( r2_hidden(D_146,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_146,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_353,plain,(
    ! [A_157] :
      ( r1_tarski(A_157,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_157,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_313,c_4])).

tff(c_363,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_353])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_122,plain,(
    ! [B_87,A_88] :
      ( k2_relat_1(B_87) = A_88
      | ~ r1_tarski(A_88,k2_relat_1(B_87))
      | ~ v5_relat_1(B_87,A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_115,c_8])).

tff(c_368,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_363,c_122])).

tff(c_374,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_151,c_368])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_374])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:45:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.34  
% 2.50/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.34  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.50/1.34  
% 2.50/1.34  %Foreground sorts:
% 2.50/1.34  
% 2.50/1.34  
% 2.50/1.34  %Background operators:
% 2.50/1.34  
% 2.50/1.34  
% 2.50/1.34  %Foreground operators:
% 2.50/1.34  tff('#skF_9', type, '#skF_9': $i > $i).
% 2.50/1.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.50/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.50/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.50/1.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.50/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.50/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.50/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.50/1.34  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.50/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.50/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.50/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.50/1.34  tff('#skF_8', type, '#skF_8': $i).
% 2.50/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.50/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.50/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.50/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.50/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.50/1.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.50/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.34  
% 2.50/1.36  tff(f_118, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 2.50/1.36  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.50/1.36  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.50/1.36  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.50/1.36  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.50/1.36  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.50/1.36  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.50/1.36  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.50/1.36  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 2.50/1.36  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.50/1.36  tff(f_42, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.50/1.36  tff(c_62, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.50/1.36  tff(c_161, plain, (![A_104, B_105, C_106]: (k2_relset_1(A_104, B_105, C_106)=k2_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.50/1.36  tff(c_165, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_62, c_161])).
% 2.50/1.36  tff(c_60, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.50/1.36  tff(c_167, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_60])).
% 2.50/1.36  tff(c_105, plain, (![C_81, A_82, B_83]: (v1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.50/1.36  tff(c_109, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_62, c_105])).
% 2.50/1.36  tff(c_147, plain, (![C_98, B_99, A_100]: (v5_relat_1(C_98, B_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.50/1.36  tff(c_151, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_62, c_147])).
% 2.50/1.36  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.50/1.36  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.50/1.36  tff(c_64, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.50/1.36  tff(c_172, plain, (![A_108, B_109, C_110]: (k1_relset_1(A_108, B_109, C_110)=k1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.50/1.36  tff(c_176, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_62, c_172])).
% 2.50/1.36  tff(c_248, plain, (![B_138, A_139, C_140]: (k1_xboole_0=B_138 | k1_relset_1(A_139, B_138, C_140)=A_139 | ~v1_funct_2(C_140, A_139, B_138) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.50/1.36  tff(c_251, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_62, c_248])).
% 2.50/1.36  tff(c_254, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_176, c_251])).
% 2.50/1.36  tff(c_261, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_254])).
% 2.50/1.36  tff(c_70, plain, (![D_69]: (r2_hidden('#skF_9'(D_69), '#skF_6') | ~r2_hidden(D_69, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.50/1.36  tff(c_125, plain, (![C_90, B_91, A_92]: (r2_hidden(C_90, B_91) | ~r2_hidden(C_90, A_92) | ~r1_tarski(A_92, B_91))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.50/1.36  tff(c_131, plain, (![D_69, B_91]: (r2_hidden('#skF_9'(D_69), B_91) | ~r1_tarski('#skF_6', B_91) | ~r2_hidden(D_69, '#skF_7'))), inference(resolution, [status(thm)], [c_70, c_125])).
% 2.50/1.36  tff(c_66, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.50/1.36  tff(c_68, plain, (![D_69]: (k1_funct_1('#skF_8', '#skF_9'(D_69))=D_69 | ~r2_hidden(D_69, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.50/1.36  tff(c_200, plain, (![A_116, D_117]: (r2_hidden(k1_funct_1(A_116, D_117), k2_relat_1(A_116)) | ~r2_hidden(D_117, k1_relat_1(A_116)) | ~v1_funct_1(A_116) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.50/1.36  tff(c_205, plain, (![D_69]: (r2_hidden(D_69, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_69), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_69, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_200])).
% 2.50/1.36  tff(c_209, plain, (![D_118]: (r2_hidden(D_118, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_118), k1_relat_1('#skF_8')) | ~r2_hidden(D_118, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_66, c_205])).
% 2.50/1.36  tff(c_214, plain, (![D_69]: (r2_hidden(D_69, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_69, '#skF_7'))), inference(resolution, [status(thm)], [c_131, c_209])).
% 2.50/1.36  tff(c_215, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_214])).
% 2.50/1.36  tff(c_262, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_261, c_215])).
% 2.50/1.36  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_262])).
% 2.50/1.36  tff(c_268, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_254])).
% 2.50/1.36  tff(c_115, plain, (![B_87, A_88]: (r1_tarski(k2_relat_1(B_87), A_88) | ~v5_relat_1(B_87, A_88) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.50/1.36  tff(c_14, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.50/1.36  tff(c_123, plain, (![B_87]: (k2_relat_1(B_87)=k1_xboole_0 | ~v5_relat_1(B_87, k1_xboole_0) | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_115, c_14])).
% 2.50/1.36  tff(c_294, plain, (![B_145]: (k2_relat_1(B_145)='#skF_7' | ~v5_relat_1(B_145, '#skF_7') | ~v1_relat_1(B_145))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_268, c_123])).
% 2.50/1.36  tff(c_297, plain, (k2_relat_1('#skF_8')='#skF_7' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_151, c_294])).
% 2.50/1.36  tff(c_300, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_297])).
% 2.50/1.36  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_300])).
% 2.50/1.36  tff(c_313, plain, (![D_146]: (r2_hidden(D_146, k2_relat_1('#skF_8')) | ~r2_hidden(D_146, '#skF_7'))), inference(splitRight, [status(thm)], [c_214])).
% 2.50/1.36  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.50/1.36  tff(c_353, plain, (![A_157]: (r1_tarski(A_157, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_157, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_313, c_4])).
% 2.50/1.36  tff(c_363, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_353])).
% 2.50/1.36  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.50/1.36  tff(c_122, plain, (![B_87, A_88]: (k2_relat_1(B_87)=A_88 | ~r1_tarski(A_88, k2_relat_1(B_87)) | ~v5_relat_1(B_87, A_88) | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_115, c_8])).
% 2.50/1.36  tff(c_368, plain, (k2_relat_1('#skF_8')='#skF_7' | ~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_363, c_122])).
% 2.50/1.36  tff(c_374, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_151, c_368])).
% 2.50/1.36  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_374])).
% 2.50/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.36  
% 2.50/1.36  Inference rules
% 2.50/1.36  ----------------------
% 2.50/1.36  #Ref     : 0
% 2.50/1.36  #Sup     : 59
% 2.50/1.36  #Fact    : 0
% 2.50/1.36  #Define  : 0
% 2.50/1.36  #Split   : 3
% 2.50/1.36  #Chain   : 0
% 2.50/1.36  #Close   : 0
% 2.50/1.36  
% 2.50/1.36  Ordering : KBO
% 2.50/1.36  
% 2.50/1.36  Simplification rules
% 2.50/1.36  ----------------------
% 2.50/1.36  #Subsume      : 4
% 2.50/1.36  #Demod        : 42
% 2.50/1.36  #Tautology    : 21
% 2.50/1.36  #SimpNegUnit  : 2
% 2.50/1.36  #BackRed      : 12
% 2.50/1.36  
% 2.50/1.36  #Partial instantiations: 0
% 2.50/1.36  #Strategies tried      : 1
% 2.50/1.36  
% 2.50/1.36  Timing (in seconds)
% 2.50/1.36  ----------------------
% 2.50/1.36  Preprocessing        : 0.34
% 2.50/1.36  Parsing              : 0.17
% 2.50/1.36  CNF conversion       : 0.03
% 2.50/1.36  Main loop            : 0.25
% 2.50/1.36  Inferencing          : 0.09
% 2.50/1.36  Reduction            : 0.07
% 2.50/1.36  Demodulation         : 0.05
% 2.50/1.36  BG Simplification    : 0.02
% 2.50/1.36  Subsumption          : 0.06
% 2.50/1.36  Abstraction          : 0.01
% 2.50/1.36  MUC search           : 0.00
% 2.50/1.36  Cooper               : 0.00
% 2.50/1.36  Total                : 0.62
% 2.50/1.36  Index Insertion      : 0.00
% 2.50/1.36  Index Deletion       : 0.00
% 2.50/1.36  Index Matching       : 0.00
% 2.50/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
