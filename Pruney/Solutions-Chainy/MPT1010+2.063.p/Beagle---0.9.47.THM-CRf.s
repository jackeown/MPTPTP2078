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
% DateTime   : Thu Dec  3 10:15:13 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 122 expanded)
%              Number of leaves         :   46 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  122 ( 220 expanded)
%              Number of equality atoms :   39 (  74 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
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

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    k1_funct_1('#skF_11','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_76,plain,(
    r2_hidden('#skF_10','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_80,plain,(
    v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_78,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k1_tarski('#skF_9')))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_348,plain,(
    ! [A_127,B_128,C_129] :
      ( k1_relset_1(A_127,B_128,C_129) = k1_relat_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_352,plain,(
    k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_78,c_348])).

tff(c_1344,plain,(
    ! [B_277,A_278,C_279] :
      ( k1_xboole_0 = B_277
      | k1_relset_1(A_278,B_277,C_279) = A_278
      | ~ v1_funct_2(C_279,A_278,B_277)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(A_278,B_277))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1351,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = '#skF_8'
    | ~ v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_78,c_1344])).

tff(c_1355,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relat_1('#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_352,c_1351])).

tff(c_1356,plain,(
    k1_relat_1('#skF_11') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1355])).

tff(c_174,plain,(
    ! [C_100,A_101,B_102] :
      ( v1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_178,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_78,c_174])).

tff(c_82,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_853,plain,(
    ! [A_191,D_192] :
      ( r2_hidden(k1_funct_1(A_191,D_192),k2_relat_1(A_191))
      | ~ r2_hidden(D_192,k1_relat_1(A_191))
      | ~ v1_funct_1(A_191)
      | ~ v1_relat_1(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_339,plain,(
    ! [A_124,B_125,C_126] :
      ( k2_relset_1(A_124,B_125,C_126) = k2_relat_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_343,plain,(
    k2_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = k2_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_78,c_339])).

tff(c_358,plain,(
    ! [A_131,B_132,C_133] :
      ( m1_subset_1(k2_relset_1(A_131,B_132,C_133),k1_zfmisc_1(B_132))
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_375,plain,
    ( m1_subset_1(k2_relat_1('#skF_11'),k1_zfmisc_1(k1_tarski('#skF_9')))
    | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k1_tarski('#skF_9')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_358])).

tff(c_381,plain,(
    m1_subset_1(k2_relat_1('#skF_11'),k1_zfmisc_1(k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_375])).

tff(c_32,plain,(
    ! [A_17,C_19,B_18] :
      ( m1_subset_1(A_17,C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(C_19))
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_384,plain,(
    ! [A_17] :
      ( m1_subset_1(A_17,k1_tarski('#skF_9'))
      | ~ r2_hidden(A_17,k2_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_381,c_32])).

tff(c_857,plain,(
    ! [D_192] :
      ( m1_subset_1(k1_funct_1('#skF_11',D_192),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_192,k1_relat_1('#skF_11'))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_853,c_384])).

tff(c_906,plain,(
    ! [D_194] :
      ( m1_subset_1(k1_funct_1('#skF_11',D_194),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_194,k1_relat_1('#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_82,c_857])).

tff(c_85,plain,(
    ! [A_80] : k2_tarski(A_80,A_80) = k1_tarski(A_80) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    ! [D_11,A_6] : r2_hidden(D_11,k2_tarski(A_6,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_91,plain,(
    ! [A_80] : r2_hidden(A_80,k1_tarski(A_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_10])).

tff(c_98,plain,(
    ! [B_82,A_83] :
      ( ~ r2_hidden(B_82,A_83)
      | ~ v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [A_80] : ~ v1_xboole_0(k1_tarski(A_80)) ),
    inference(resolution,[status(thm)],[c_91,c_98])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_194,plain,(
    ! [D_107,B_108,A_109] :
      ( D_107 = B_108
      | D_107 = A_109
      | ~ r2_hidden(D_107,k2_tarski(A_109,B_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_222,plain,(
    ! [D_110,A_111] :
      ( D_110 = A_111
      | D_110 = A_111
      | ~ r2_hidden(D_110,k1_tarski(A_111)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_194])).

tff(c_226,plain,(
    ! [A_15,A_111] :
      ( A_15 = A_111
      | v1_xboole_0(k1_tarski(A_111))
      | ~ m1_subset_1(A_15,k1_tarski(A_111)) ) ),
    inference(resolution,[status(thm)],[c_30,c_222])).

tff(c_236,plain,(
    ! [A_15,A_111] :
      ( A_15 = A_111
      | ~ m1_subset_1(A_15,k1_tarski(A_111)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_226])).

tff(c_910,plain,(
    ! [D_194] :
      ( k1_funct_1('#skF_11',D_194) = '#skF_9'
      | ~ r2_hidden(D_194,k1_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_906,c_236])).

tff(c_1460,plain,(
    ! [D_282] :
      ( k1_funct_1('#skF_11',D_282) = '#skF_9'
      | ~ r2_hidden(D_282,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1356,c_910])).

tff(c_1477,plain,(
    k1_funct_1('#skF_11','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_76,c_1460])).

tff(c_1488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1477])).

tff(c_1489,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1355])).

tff(c_129,plain,(
    ! [B_90,A_91] :
      ( ~ r1_tarski(B_90,A_91)
      | ~ r2_hidden(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_147,plain,(
    ! [A_80] : ~ r1_tarski(k1_tarski(A_80),A_80) ),
    inference(resolution,[status(thm)],[c_91,c_129])).

tff(c_1514,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1489,c_147])).

tff(c_1524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1514])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:20:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.64  
% 3.48/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.64  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 3.48/1.64  
% 3.48/1.64  %Foreground sorts:
% 3.48/1.64  
% 3.48/1.64  
% 3.48/1.64  %Background operators:
% 3.48/1.64  
% 3.48/1.64  
% 3.48/1.64  %Foreground operators:
% 3.48/1.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.48/1.64  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.48/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.48/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.64  tff('#skF_11', type, '#skF_11': $i).
% 3.48/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.48/1.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.48/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.64  tff('#skF_10', type, '#skF_10': $i).
% 3.48/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.48/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.48/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.48/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.48/1.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.48/1.64  tff('#skF_9', type, '#skF_9': $i).
% 3.48/1.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.48/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.64  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.48/1.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.48/1.64  tff('#skF_8', type, '#skF_8': $i).
% 3.48/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.48/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.48/1.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.48/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.48/1.64  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.48/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.48/1.64  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.48/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.64  
% 3.82/1.65  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.82/1.65  tff(f_123, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.82/1.65  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.82/1.65  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.82/1.65  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.82/1.65  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.82/1.65  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.82/1.65  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.82/1.65  tff(f_58, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.82/1.65  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.82/1.65  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.82/1.65  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.82/1.65  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.82/1.65  tff(f_78, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.82/1.65  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.82/1.65  tff(c_74, plain, (k1_funct_1('#skF_11', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.82/1.65  tff(c_76, plain, (r2_hidden('#skF_10', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.82/1.65  tff(c_80, plain, (v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.82/1.65  tff(c_78, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.82/1.65  tff(c_348, plain, (![A_127, B_128, C_129]: (k1_relset_1(A_127, B_128, C_129)=k1_relat_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.82/1.65  tff(c_352, plain, (k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_78, c_348])).
% 3.82/1.65  tff(c_1344, plain, (![B_277, A_278, C_279]: (k1_xboole_0=B_277 | k1_relset_1(A_278, B_277, C_279)=A_278 | ~v1_funct_2(C_279, A_278, B_277) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(A_278, B_277))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.82/1.65  tff(c_1351, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')='#skF_8' | ~v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_78, c_1344])).
% 3.82/1.65  tff(c_1355, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relat_1('#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_352, c_1351])).
% 3.82/1.65  tff(c_1356, plain, (k1_relat_1('#skF_11')='#skF_8'), inference(splitLeft, [status(thm)], [c_1355])).
% 3.82/1.65  tff(c_174, plain, (![C_100, A_101, B_102]: (v1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.82/1.65  tff(c_178, plain, (v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_78, c_174])).
% 3.82/1.65  tff(c_82, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.82/1.65  tff(c_853, plain, (![A_191, D_192]: (r2_hidden(k1_funct_1(A_191, D_192), k2_relat_1(A_191)) | ~r2_hidden(D_192, k1_relat_1(A_191)) | ~v1_funct_1(A_191) | ~v1_relat_1(A_191))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.82/1.65  tff(c_339, plain, (![A_124, B_125, C_126]: (k2_relset_1(A_124, B_125, C_126)=k2_relat_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.82/1.65  tff(c_343, plain, (k2_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')=k2_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_78, c_339])).
% 3.82/1.65  tff(c_358, plain, (![A_131, B_132, C_133]: (m1_subset_1(k2_relset_1(A_131, B_132, C_133), k1_zfmisc_1(B_132)) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.82/1.65  tff(c_375, plain, (m1_subset_1(k2_relat_1('#skF_11'), k1_zfmisc_1(k1_tarski('#skF_9'))) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))), inference(superposition, [status(thm), theory('equality')], [c_343, c_358])).
% 3.82/1.65  tff(c_381, plain, (m1_subset_1(k2_relat_1('#skF_11'), k1_zfmisc_1(k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_375])).
% 3.82/1.65  tff(c_32, plain, (![A_17, C_19, B_18]: (m1_subset_1(A_17, C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(C_19)) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.82/1.65  tff(c_384, plain, (![A_17]: (m1_subset_1(A_17, k1_tarski('#skF_9')) | ~r2_hidden(A_17, k2_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_381, c_32])).
% 3.82/1.65  tff(c_857, plain, (![D_192]: (m1_subset_1(k1_funct_1('#skF_11', D_192), k1_tarski('#skF_9')) | ~r2_hidden(D_192, k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_853, c_384])).
% 3.82/1.65  tff(c_906, plain, (![D_194]: (m1_subset_1(k1_funct_1('#skF_11', D_194), k1_tarski('#skF_9')) | ~r2_hidden(D_194, k1_relat_1('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_82, c_857])).
% 3.82/1.65  tff(c_85, plain, (![A_80]: (k2_tarski(A_80, A_80)=k1_tarski(A_80))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.82/1.65  tff(c_10, plain, (![D_11, A_6]: (r2_hidden(D_11, k2_tarski(A_6, D_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.82/1.65  tff(c_91, plain, (![A_80]: (r2_hidden(A_80, k1_tarski(A_80)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_10])).
% 3.82/1.65  tff(c_98, plain, (![B_82, A_83]: (~r2_hidden(B_82, A_83) | ~v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.82/1.65  tff(c_108, plain, (![A_80]: (~v1_xboole_0(k1_tarski(A_80)))), inference(resolution, [status(thm)], [c_91, c_98])).
% 3.82/1.65  tff(c_30, plain, (![A_15, B_16]: (r2_hidden(A_15, B_16) | v1_xboole_0(B_16) | ~m1_subset_1(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.82/1.65  tff(c_26, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.82/1.65  tff(c_194, plain, (![D_107, B_108, A_109]: (D_107=B_108 | D_107=A_109 | ~r2_hidden(D_107, k2_tarski(A_109, B_108)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.82/1.65  tff(c_222, plain, (![D_110, A_111]: (D_110=A_111 | D_110=A_111 | ~r2_hidden(D_110, k1_tarski(A_111)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_194])).
% 3.82/1.65  tff(c_226, plain, (![A_15, A_111]: (A_15=A_111 | v1_xboole_0(k1_tarski(A_111)) | ~m1_subset_1(A_15, k1_tarski(A_111)))), inference(resolution, [status(thm)], [c_30, c_222])).
% 3.82/1.65  tff(c_236, plain, (![A_15, A_111]: (A_15=A_111 | ~m1_subset_1(A_15, k1_tarski(A_111)))), inference(negUnitSimplification, [status(thm)], [c_108, c_226])).
% 3.82/1.65  tff(c_910, plain, (![D_194]: (k1_funct_1('#skF_11', D_194)='#skF_9' | ~r2_hidden(D_194, k1_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_906, c_236])).
% 3.82/1.65  tff(c_1460, plain, (![D_282]: (k1_funct_1('#skF_11', D_282)='#skF_9' | ~r2_hidden(D_282, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1356, c_910])).
% 3.82/1.65  tff(c_1477, plain, (k1_funct_1('#skF_11', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_76, c_1460])).
% 3.82/1.65  tff(c_1488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1477])).
% 3.82/1.65  tff(c_1489, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1355])).
% 3.82/1.65  tff(c_129, plain, (![B_90, A_91]: (~r1_tarski(B_90, A_91) | ~r2_hidden(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.82/1.65  tff(c_147, plain, (![A_80]: (~r1_tarski(k1_tarski(A_80), A_80))), inference(resolution, [status(thm)], [c_91, c_129])).
% 3.82/1.65  tff(c_1514, plain, (~r1_tarski(k1_xboole_0, '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1489, c_147])).
% 3.82/1.65  tff(c_1524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1514])).
% 3.82/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.65  
% 3.82/1.65  Inference rules
% 3.82/1.65  ----------------------
% 3.82/1.65  #Ref     : 0
% 3.82/1.65  #Sup     : 285
% 3.82/1.65  #Fact    : 2
% 3.82/1.65  #Define  : 0
% 3.82/1.65  #Split   : 7
% 3.82/1.65  #Chain   : 0
% 3.82/1.65  #Close   : 0
% 3.82/1.65  
% 3.82/1.65  Ordering : KBO
% 3.82/1.65  
% 3.82/1.65  Simplification rules
% 3.82/1.65  ----------------------
% 3.82/1.65  #Subsume      : 62
% 3.82/1.65  #Demod        : 150
% 3.82/1.65  #Tautology    : 83
% 3.82/1.65  #SimpNegUnit  : 24
% 3.82/1.65  #BackRed      : 27
% 3.82/1.65  
% 3.82/1.65  #Partial instantiations: 0
% 3.82/1.65  #Strategies tried      : 1
% 3.82/1.65  
% 3.82/1.65  Timing (in seconds)
% 3.82/1.65  ----------------------
% 3.82/1.66  Preprocessing        : 0.37
% 3.82/1.66  Parsing              : 0.19
% 3.82/1.66  CNF conversion       : 0.03
% 3.82/1.66  Main loop            : 0.49
% 3.82/1.66  Inferencing          : 0.18
% 3.82/1.66  Reduction            : 0.15
% 3.82/1.66  Demodulation         : 0.10
% 3.82/1.66  BG Simplification    : 0.03
% 3.82/1.66  Subsumption          : 0.09
% 3.82/1.66  Abstraction          : 0.03
% 3.82/1.66  MUC search           : 0.00
% 3.82/1.66  Cooper               : 0.00
% 3.82/1.66  Total                : 0.89
% 3.82/1.66  Index Insertion      : 0.00
% 3.82/1.66  Index Deletion       : 0.00
% 3.82/1.66  Index Matching       : 0.00
% 3.82/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
