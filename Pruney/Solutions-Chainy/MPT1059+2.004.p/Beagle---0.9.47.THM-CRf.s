%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:33 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 116 expanded)
%              Number of leaves         :   43 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  124 ( 277 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_204,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_184,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_84,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_160,axiom,(
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

tff(f_171,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_100,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_98,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_96,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_94,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_102,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_92,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_1433,plain,(
    ! [A_257,B_258,C_259,D_260] :
      ( k3_funct_2(A_257,B_258,C_259,D_260) = k1_funct_1(C_259,D_260)
      | ~ m1_subset_1(D_260,A_257)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258)))
      | ~ v1_funct_2(C_259,A_257,B_258)
      | ~ v1_funct_1(C_259)
      | v1_xboole_0(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_1443,plain,(
    ! [B_258,C_259] :
      ( k3_funct_2('#skF_6',B_258,C_259,'#skF_9') = k1_funct_1(C_259,'#skF_9')
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_258)))
      | ~ v1_funct_2(C_259,'#skF_6',B_258)
      | ~ v1_funct_1(C_259)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_92,c_1433])).

tff(c_1480,plain,(
    ! [B_261,C_262] :
      ( k3_funct_2('#skF_6',B_261,C_262,'#skF_9') = k1_funct_1(C_262,'#skF_9')
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_261)))
      | ~ v1_funct_2(C_262,'#skF_6',B_261)
      | ~ v1_funct_1(C_262) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_1443])).

tff(c_1491,plain,
    ( k3_funct_2('#skF_6','#skF_7','#skF_8','#skF_9') = k1_funct_1('#skF_8','#skF_9')
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_94,c_1480])).

tff(c_1496,plain,(
    k3_funct_2('#skF_6','#skF_7','#skF_8','#skF_9') = k1_funct_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_1491])).

tff(c_90,plain,(
    k3_funct_2('#skF_6','#skF_7','#skF_8','#skF_9') != k7_partfun1('#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_1708,plain,(
    k7_partfun1('#skF_7','#skF_8','#skF_9') != k1_funct_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1496,c_90])).

tff(c_277,plain,(
    ! [C_119,B_120,A_121] :
      ( v5_relat_1(C_119,B_120)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_121,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_286,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_94,c_277])).

tff(c_18,plain,(
    ! [B_9,A_8] :
      ( r2_hidden(B_9,A_8)
      | ~ m1_subset_1(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    ! [A_34,B_35] : v1_relat_1(k2_zfmisc_1(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_160,plain,(
    ! [B_93,A_94] :
      ( v1_relat_1(B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_94))
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_167,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_94,c_160])).

tff(c_171,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_167])).

tff(c_366,plain,(
    ! [A_135,B_136,C_137] :
      ( k1_relset_1(A_135,B_136,C_137) = k1_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_375,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_94,c_366])).

tff(c_742,plain,(
    ! [B_210,A_211,C_212] :
      ( k1_xboole_0 = B_210
      | k1_relset_1(A_211,B_210,C_212) = A_211
      | ~ v1_funct_2(C_212,A_211,B_210)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_211,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_753,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_94,c_742])).

tff(c_758,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_375,c_753])).

tff(c_759,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_758])).

tff(c_1099,plain,(
    ! [A_242,B_243,C_244] :
      ( k7_partfun1(A_242,B_243,C_244) = k1_funct_1(B_243,C_244)
      | ~ r2_hidden(C_244,k1_relat_1(B_243))
      | ~ v1_funct_1(B_243)
      | ~ v5_relat_1(B_243,A_242)
      | ~ v1_relat_1(B_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1107,plain,(
    ! [A_242,C_244] :
      ( k7_partfun1(A_242,'#skF_8',C_244) = k1_funct_1('#skF_8',C_244)
      | ~ r2_hidden(C_244,'#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',A_242)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_1099])).

tff(c_1255,plain,(
    ! [A_247,C_248] :
      ( k7_partfun1(A_247,'#skF_8',C_248) = k1_funct_1('#skF_8',C_248)
      | ~ r2_hidden(C_248,'#skF_6')
      | ~ v5_relat_1('#skF_8',A_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_98,c_1107])).

tff(c_1267,plain,(
    ! [A_247,B_9] :
      ( k7_partfun1(A_247,'#skF_8',B_9) = k1_funct_1('#skF_8',B_9)
      | ~ v5_relat_1('#skF_8',A_247)
      | ~ m1_subset_1(B_9,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_18,c_1255])).

tff(c_1306,plain,(
    ! [A_253,B_254] :
      ( k7_partfun1(A_253,'#skF_8',B_254) = k1_funct_1('#skF_8',B_254)
      | ~ v5_relat_1('#skF_8',A_253)
      | ~ m1_subset_1(B_254,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_1267])).

tff(c_1834,plain,(
    ! [B_278] :
      ( k7_partfun1('#skF_7','#skF_8',B_278) = k1_funct_1('#skF_8',B_278)
      | ~ m1_subset_1(B_278,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_286,c_1306])).

tff(c_1845,plain,(
    k7_partfun1('#skF_7','#skF_8','#skF_9') = k1_funct_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_92,c_1834])).

tff(c_1853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1708,c_1845])).

tff(c_1854,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_758])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1870,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1854,c_8])).

tff(c_1872,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_1870])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:50 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.67  
% 3.86/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.67  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 3.86/1.67  
% 3.86/1.67  %Foreground sorts:
% 3.86/1.67  
% 3.86/1.67  
% 3.86/1.67  %Background operators:
% 3.86/1.67  
% 3.86/1.67  
% 3.86/1.67  %Foreground operators:
% 3.86/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.86/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.86/1.67  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.86/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.86/1.67  tff('#skF_7', type, '#skF_7': $i).
% 3.86/1.67  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.86/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.86/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.86/1.67  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.86/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.86/1.67  tff('#skF_6', type, '#skF_6': $i).
% 3.86/1.67  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.86/1.67  tff('#skF_9', type, '#skF_9': $i).
% 3.86/1.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.86/1.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.86/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.86/1.67  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.86/1.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.86/1.67  tff('#skF_8', type, '#skF_8': $i).
% 3.86/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.86/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.86/1.67  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.86/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.86/1.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.86/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.86/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.86/1.67  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.86/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.86/1.67  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.86/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.86/1.67  
% 3.86/1.68  tff(f_204, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 3.86/1.68  tff(f_184, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.86/1.68  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.86/1.68  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.86/1.68  tff(f_84, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.86/1.68  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.86/1.68  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.86/1.68  tff(f_160, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.86/1.68  tff(f_171, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 3.86/1.68  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.86/1.68  tff(c_100, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.86/1.68  tff(c_98, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.86/1.68  tff(c_96, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.86/1.68  tff(c_94, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.86/1.68  tff(c_102, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.86/1.68  tff(c_92, plain, (m1_subset_1('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.86/1.68  tff(c_1433, plain, (![A_257, B_258, C_259, D_260]: (k3_funct_2(A_257, B_258, C_259, D_260)=k1_funct_1(C_259, D_260) | ~m1_subset_1(D_260, A_257) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))) | ~v1_funct_2(C_259, A_257, B_258) | ~v1_funct_1(C_259) | v1_xboole_0(A_257))), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.86/1.68  tff(c_1443, plain, (![B_258, C_259]: (k3_funct_2('#skF_6', B_258, C_259, '#skF_9')=k1_funct_1(C_259, '#skF_9') | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_258))) | ~v1_funct_2(C_259, '#skF_6', B_258) | ~v1_funct_1(C_259) | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_92, c_1433])).
% 3.86/1.68  tff(c_1480, plain, (![B_261, C_262]: (k3_funct_2('#skF_6', B_261, C_262, '#skF_9')=k1_funct_1(C_262, '#skF_9') | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_261))) | ~v1_funct_2(C_262, '#skF_6', B_261) | ~v1_funct_1(C_262))), inference(negUnitSimplification, [status(thm)], [c_102, c_1443])).
% 3.86/1.68  tff(c_1491, plain, (k3_funct_2('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k1_funct_1('#skF_8', '#skF_9') | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_94, c_1480])).
% 3.86/1.68  tff(c_1496, plain, (k3_funct_2('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k1_funct_1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_1491])).
% 3.86/1.68  tff(c_90, plain, (k3_funct_2('#skF_6', '#skF_7', '#skF_8', '#skF_9')!=k7_partfun1('#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.86/1.68  tff(c_1708, plain, (k7_partfun1('#skF_7', '#skF_8', '#skF_9')!=k1_funct_1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1496, c_90])).
% 3.86/1.68  tff(c_277, plain, (![C_119, B_120, A_121]: (v5_relat_1(C_119, B_120) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_121, B_120))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.86/1.68  tff(c_286, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_94, c_277])).
% 3.86/1.68  tff(c_18, plain, (![B_9, A_8]: (r2_hidden(B_9, A_8) | ~m1_subset_1(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.86/1.68  tff(c_42, plain, (![A_34, B_35]: (v1_relat_1(k2_zfmisc_1(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.86/1.68  tff(c_160, plain, (![B_93, A_94]: (v1_relat_1(B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(A_94)) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.86/1.68  tff(c_167, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_94, c_160])).
% 3.86/1.68  tff(c_171, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_167])).
% 3.86/1.68  tff(c_366, plain, (![A_135, B_136, C_137]: (k1_relset_1(A_135, B_136, C_137)=k1_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.86/1.68  tff(c_375, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_94, c_366])).
% 3.86/1.68  tff(c_742, plain, (![B_210, A_211, C_212]: (k1_xboole_0=B_210 | k1_relset_1(A_211, B_210, C_212)=A_211 | ~v1_funct_2(C_212, A_211, B_210) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_211, B_210))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.86/1.68  tff(c_753, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_94, c_742])).
% 3.86/1.68  tff(c_758, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_375, c_753])).
% 3.86/1.68  tff(c_759, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_758])).
% 3.86/1.68  tff(c_1099, plain, (![A_242, B_243, C_244]: (k7_partfun1(A_242, B_243, C_244)=k1_funct_1(B_243, C_244) | ~r2_hidden(C_244, k1_relat_1(B_243)) | ~v1_funct_1(B_243) | ~v5_relat_1(B_243, A_242) | ~v1_relat_1(B_243))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.86/1.68  tff(c_1107, plain, (![A_242, C_244]: (k7_partfun1(A_242, '#skF_8', C_244)=k1_funct_1('#skF_8', C_244) | ~r2_hidden(C_244, '#skF_6') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', A_242) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_759, c_1099])).
% 3.86/1.68  tff(c_1255, plain, (![A_247, C_248]: (k7_partfun1(A_247, '#skF_8', C_248)=k1_funct_1('#skF_8', C_248) | ~r2_hidden(C_248, '#skF_6') | ~v5_relat_1('#skF_8', A_247))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_98, c_1107])).
% 3.86/1.68  tff(c_1267, plain, (![A_247, B_9]: (k7_partfun1(A_247, '#skF_8', B_9)=k1_funct_1('#skF_8', B_9) | ~v5_relat_1('#skF_8', A_247) | ~m1_subset_1(B_9, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_18, c_1255])).
% 3.86/1.68  tff(c_1306, plain, (![A_253, B_254]: (k7_partfun1(A_253, '#skF_8', B_254)=k1_funct_1('#skF_8', B_254) | ~v5_relat_1('#skF_8', A_253) | ~m1_subset_1(B_254, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_102, c_1267])).
% 3.86/1.68  tff(c_1834, plain, (![B_278]: (k7_partfun1('#skF_7', '#skF_8', B_278)=k1_funct_1('#skF_8', B_278) | ~m1_subset_1(B_278, '#skF_6'))), inference(resolution, [status(thm)], [c_286, c_1306])).
% 3.86/1.68  tff(c_1845, plain, (k7_partfun1('#skF_7', '#skF_8', '#skF_9')=k1_funct_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_92, c_1834])).
% 3.86/1.68  tff(c_1853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1708, c_1845])).
% 3.86/1.68  tff(c_1854, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_758])).
% 3.86/1.68  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.86/1.68  tff(c_1870, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1854, c_8])).
% 3.86/1.68  tff(c_1872, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_1870])).
% 3.86/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.68  
% 3.86/1.68  Inference rules
% 3.86/1.68  ----------------------
% 3.86/1.68  #Ref     : 0
% 3.86/1.68  #Sup     : 375
% 3.86/1.68  #Fact    : 0
% 3.86/1.68  #Define  : 0
% 3.86/1.68  #Split   : 7
% 3.86/1.68  #Chain   : 0
% 3.86/1.68  #Close   : 0
% 3.86/1.68  
% 3.86/1.68  Ordering : KBO
% 3.86/1.68  
% 3.86/1.68  Simplification rules
% 3.86/1.68  ----------------------
% 3.86/1.68  #Subsume      : 103
% 3.86/1.68  #Demod        : 223
% 3.86/1.68  #Tautology    : 79
% 3.86/1.68  #SimpNegUnit  : 13
% 3.86/1.68  #BackRed      : 18
% 3.86/1.68  
% 3.86/1.68  #Partial instantiations: 0
% 3.86/1.68  #Strategies tried      : 1
% 3.86/1.68  
% 3.86/1.68  Timing (in seconds)
% 3.86/1.68  ----------------------
% 3.86/1.69  Preprocessing        : 0.38
% 3.86/1.69  Parsing              : 0.20
% 3.86/1.69  CNF conversion       : 0.03
% 3.86/1.69  Main loop            : 0.55
% 3.86/1.69  Inferencing          : 0.19
% 3.86/1.69  Reduction            : 0.17
% 3.86/1.69  Demodulation         : 0.11
% 3.86/1.69  BG Simplification    : 0.03
% 3.86/1.69  Subsumption          : 0.12
% 3.86/1.69  Abstraction          : 0.02
% 3.86/1.69  MUC search           : 0.00
% 3.86/1.69  Cooper               : 0.00
% 3.86/1.69  Total                : 0.96
% 3.86/1.69  Index Insertion      : 0.00
% 3.86/1.69  Index Deletion       : 0.00
% 3.86/1.69  Index Matching       : 0.00
% 3.86/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
