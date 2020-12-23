%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:18 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 180 expanded)
%              Number of leaves         :   32 (  74 expanded)
%              Depth                    :   11
%              Number of atoms          :  109 ( 430 expanded)
%              Number of equality atoms :   33 ( 169 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => r2_hidden(C,k1_funct_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_63,axiom,(
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

tff(f_79,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

tff(c_66,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_72,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_72])).

tff(c_77,plain,(
    ! [C_38,B_39,A_40] :
      ( v5_relat_1(C_38,B_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_40,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_81,plain,(
    v5_relat_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_77])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_71,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_68,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_94,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_98,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_94])).

tff(c_153,plain,(
    ! [B_90,A_91,C_92] :
      ( k1_xboole_0 = B_90
      | k1_relset_1(A_91,B_90,C_92) = A_91
      | ~ v1_funct_2(C_92,A_91,B_90)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_156,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_153])).

tff(c_159,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_98,c_156])).

tff(c_160,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_159])).

tff(c_26,plain,(
    ! [E_34,B_16] :
      ( r2_hidden(E_34,k1_funct_2(k1_relat_1(E_34),B_16))
      | ~ r1_tarski(k2_relat_1(E_34),B_16)
      | ~ v1_funct_1(E_34)
      | ~ v1_relat_1(E_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_165,plain,(
    ! [B_16] :
      ( r2_hidden('#skF_7',k1_funct_2('#skF_5',B_16))
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_16)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_26])).

tff(c_175,plain,(
    ! [B_93] :
      ( r2_hidden('#skF_7',k1_funct_2('#skF_5',B_93))
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_165])).

tff(c_62,plain,(
    ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_182,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_175,c_62])).

tff(c_194,plain,
    ( ~ v5_relat_1('#skF_7','#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_182])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_81,c_194])).

tff(c_200,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_199,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_205,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_199])).

tff(c_216,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_66])).

tff(c_217,plain,(
    ! [C_97,A_98,B_99] :
      ( v1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_221,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_216,c_217])).

tff(c_233,plain,(
    ! [C_107,B_108,A_109] :
      ( v5_relat_1(C_107,B_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_237,plain,(
    v5_relat_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_216,c_233])).

tff(c_211,plain,(
    v1_funct_2('#skF_7','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_68])).

tff(c_238,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_relset_1(A_110,B_111,C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_242,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_216,c_238])).

tff(c_22,plain,(
    ! [B_13,C_14] :
      ( k1_relset_1(k1_xboole_0,B_13,C_14) = k1_xboole_0
      | ~ v1_funct_2(C_14,k1_xboole_0,B_13)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_295,plain,(
    ! [B_138,C_139] :
      ( k1_relset_1('#skF_6',B_138,C_139) = '#skF_6'
      | ~ v1_funct_2(C_139,'#skF_6',B_138)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_138))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_200,c_200,c_200,c_22])).

tff(c_298,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_7') = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_216,c_295])).

tff(c_301,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_242,c_298])).

tff(c_311,plain,(
    ! [B_16] :
      ( r2_hidden('#skF_7',k1_funct_2('#skF_6',B_16))
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_16)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_26])).

tff(c_321,plain,(
    ! [B_143] :
      ( r2_hidden('#skF_7',k1_funct_2('#skF_6',B_143))
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_70,c_311])).

tff(c_210,plain,(
    ~ r2_hidden('#skF_7',k1_funct_2('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_62])).

tff(c_328,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_321,c_210])).

tff(c_331,plain,
    ( ~ v5_relat_1('#skF_7','#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_328])).

tff(c_335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_237,c_331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.51  
% 2.51/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.51  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.51/1.51  
% 2.51/1.51  %Foreground sorts:
% 2.51/1.51  
% 2.51/1.51  
% 2.51/1.51  %Background operators:
% 2.51/1.51  
% 2.51/1.51  
% 2.51/1.51  %Foreground operators:
% 2.51/1.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.51/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.51/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.51  tff('#skF_7', type, '#skF_7': $i).
% 2.51/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.51/1.51  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.51/1.51  tff('#skF_6', type, '#skF_6': $i).
% 2.51/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.51/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.51/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.51/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.51/1.51  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 2.51/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.51/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.51/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.51/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.51/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.51  
% 2.51/1.52  tff(f_92, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => r2_hidden(C, k1_funct_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_funct_2)).
% 2.51/1.52  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.51/1.52  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.51/1.52  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.51/1.52  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.51/1.52  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.51/1.52  tff(f_79, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 2.51/1.52  tff(c_66, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.51/1.52  tff(c_72, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.52  tff(c_76, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_66, c_72])).
% 2.51/1.52  tff(c_77, plain, (![C_38, B_39, A_40]: (v5_relat_1(C_38, B_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_40, B_39))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.52  tff(c_81, plain, (v5_relat_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_77])).
% 2.51/1.52  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.52  tff(c_70, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.51/1.52  tff(c_64, plain, (k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.51/1.52  tff(c_71, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_64])).
% 2.51/1.52  tff(c_68, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.51/1.52  tff(c_94, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.51/1.52  tff(c_98, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_66, c_94])).
% 2.51/1.52  tff(c_153, plain, (![B_90, A_91, C_92]: (k1_xboole_0=B_90 | k1_relset_1(A_91, B_90, C_92)=A_91 | ~v1_funct_2(C_92, A_91, B_90) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.51/1.52  tff(c_156, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_153])).
% 2.51/1.52  tff(c_159, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_98, c_156])).
% 2.51/1.52  tff(c_160, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_71, c_159])).
% 2.51/1.52  tff(c_26, plain, (![E_34, B_16]: (r2_hidden(E_34, k1_funct_2(k1_relat_1(E_34), B_16)) | ~r1_tarski(k2_relat_1(E_34), B_16) | ~v1_funct_1(E_34) | ~v1_relat_1(E_34))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.51/1.52  tff(c_165, plain, (![B_16]: (r2_hidden('#skF_7', k1_funct_2('#skF_5', B_16)) | ~r1_tarski(k2_relat_1('#skF_7'), B_16) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_160, c_26])).
% 2.51/1.52  tff(c_175, plain, (![B_93]: (r2_hidden('#skF_7', k1_funct_2('#skF_5', B_93)) | ~r1_tarski(k2_relat_1('#skF_7'), B_93))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70, c_165])).
% 2.51/1.52  tff(c_62, plain, (~r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.51/1.52  tff(c_182, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_175, c_62])).
% 2.51/1.52  tff(c_194, plain, (~v5_relat_1('#skF_7', '#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_4, c_182])).
% 2.51/1.52  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_81, c_194])).
% 2.51/1.52  tff(c_200, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_64])).
% 2.51/1.52  tff(c_199, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_64])).
% 2.51/1.52  tff(c_205, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_199])).
% 2.51/1.52  tff(c_216, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_66])).
% 2.51/1.52  tff(c_217, plain, (![C_97, A_98, B_99]: (v1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.52  tff(c_221, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_216, c_217])).
% 2.51/1.52  tff(c_233, plain, (![C_107, B_108, A_109]: (v5_relat_1(C_107, B_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.52  tff(c_237, plain, (v5_relat_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_216, c_233])).
% 2.51/1.52  tff(c_211, plain, (v1_funct_2('#skF_7', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_205, c_68])).
% 2.51/1.52  tff(c_238, plain, (![A_110, B_111, C_112]: (k1_relset_1(A_110, B_111, C_112)=k1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.51/1.52  tff(c_242, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_216, c_238])).
% 2.51/1.52  tff(c_22, plain, (![B_13, C_14]: (k1_relset_1(k1_xboole_0, B_13, C_14)=k1_xboole_0 | ~v1_funct_2(C_14, k1_xboole_0, B_13) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_13))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.51/1.52  tff(c_295, plain, (![B_138, C_139]: (k1_relset_1('#skF_6', B_138, C_139)='#skF_6' | ~v1_funct_2(C_139, '#skF_6', B_138) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_138))))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_200, c_200, c_200, c_22])).
% 2.51/1.52  tff(c_298, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_7')='#skF_6' | ~v1_funct_2('#skF_7', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_216, c_295])).
% 2.51/1.52  tff(c_301, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_242, c_298])).
% 2.51/1.52  tff(c_311, plain, (![B_16]: (r2_hidden('#skF_7', k1_funct_2('#skF_6', B_16)) | ~r1_tarski(k2_relat_1('#skF_7'), B_16) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_301, c_26])).
% 2.51/1.52  tff(c_321, plain, (![B_143]: (r2_hidden('#skF_7', k1_funct_2('#skF_6', B_143)) | ~r1_tarski(k2_relat_1('#skF_7'), B_143))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_70, c_311])).
% 2.51/1.52  tff(c_210, plain, (~r2_hidden('#skF_7', k1_funct_2('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_62])).
% 2.51/1.52  tff(c_328, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_321, c_210])).
% 2.51/1.52  tff(c_331, plain, (~v5_relat_1('#skF_7', '#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_4, c_328])).
% 2.51/1.52  tff(c_335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_237, c_331])).
% 2.51/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.52  
% 2.51/1.52  Inference rules
% 2.51/1.52  ----------------------
% 2.51/1.52  #Ref     : 0
% 2.51/1.52  #Sup     : 58
% 2.51/1.52  #Fact    : 0
% 2.51/1.52  #Define  : 0
% 2.51/1.52  #Split   : 1
% 2.51/1.52  #Chain   : 0
% 2.51/1.52  #Close   : 0
% 2.51/1.52  
% 2.51/1.52  Ordering : KBO
% 2.51/1.52  
% 2.51/1.52  Simplification rules
% 2.51/1.52  ----------------------
% 2.51/1.52  #Subsume      : 0
% 2.51/1.52  #Demod        : 40
% 2.51/1.52  #Tautology    : 27
% 2.51/1.52  #SimpNegUnit  : 2
% 2.51/1.52  #BackRed      : 5
% 2.51/1.52  
% 2.51/1.52  #Partial instantiations: 0
% 2.51/1.52  #Strategies tried      : 1
% 2.51/1.52  
% 2.51/1.52  Timing (in seconds)
% 2.51/1.52  ----------------------
% 2.51/1.53  Preprocessing        : 0.44
% 2.51/1.53  Parsing              : 0.25
% 2.51/1.53  CNF conversion       : 0.02
% 2.51/1.53  Main loop            : 0.23
% 2.51/1.53  Inferencing          : 0.09
% 2.51/1.53  Reduction            : 0.07
% 2.51/1.53  Demodulation         : 0.05
% 2.51/1.53  BG Simplification    : 0.02
% 2.51/1.53  Subsumption          : 0.03
% 2.70/1.53  Abstraction          : 0.01
% 2.70/1.53  MUC search           : 0.00
% 2.70/1.53  Cooper               : 0.00
% 2.70/1.53  Total                : 0.71
% 2.70/1.53  Index Insertion      : 0.00
% 2.70/1.53  Index Deletion       : 0.00
% 2.70/1.53  Index Matching       : 0.00
% 2.70/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
