%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:00 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   59 (  75 expanded)
%              Number of leaves         :   35 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   82 ( 145 expanded)
%              Number of equality atoms :   20 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
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

tff(f_53,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_56,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_69,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_73,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_69])).

tff(c_102,plain,(
    ! [C_80,B_81,A_82] :
      ( v5_relat_1(C_80,B_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_106,plain,(
    v5_relat_1('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_102])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_54,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_58,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_124,plain,(
    ! [A_89,B_90,C_91] :
      ( k1_relset_1(A_89,B_90,C_91) = k1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_128,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_124])).

tff(c_165,plain,(
    ! [B_112,A_113,C_114] :
      ( k1_xboole_0 = B_112
      | k1_relset_1(A_113,B_112,C_114) = A_113
      | ~ v1_funct_2(C_114,A_113,B_112)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_168,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_165])).

tff(c_171,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_128,c_168])).

tff(c_172,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_171])).

tff(c_133,plain,(
    ! [A_92,D_93] :
      ( r2_hidden(k1_funct_1(A_92,D_93),k2_relat_1(A_92))
      | ~ r2_hidden(D_93,k1_relat_1(A_92))
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_202,plain,(
    ! [A_121,D_122,B_123] :
      ( r2_hidden(k1_funct_1(A_121,D_122),B_123)
      | ~ r1_tarski(k2_relat_1(A_121),B_123)
      | ~ r2_hidden(D_122,k1_relat_1(A_121))
      | ~ v1_funct_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(resolution,[status(thm)],[c_133,c_2])).

tff(c_50,plain,(
    ~ r2_hidden(k1_funct_1('#skF_9','#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_207,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_7')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_202,c_50])).

tff(c_214,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_60,c_54,c_172,c_207])).

tff(c_217,plain,
    ( ~ v5_relat_1('#skF_9','#skF_7')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_10,c_214])).

tff(c_221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_106,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.34  
% 2.47/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.35  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.47/1.35  
% 2.47/1.35  %Foreground sorts:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Background operators:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Foreground operators:
% 2.47/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.47/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.47/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.47/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.47/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.47/1.35  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.47/1.35  tff('#skF_9', type, '#skF_9': $i).
% 2.47/1.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.47/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.47/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.47/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.47/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.47/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.47/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.47/1.35  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.47/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.35  
% 2.47/1.36  tff(f_98, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.47/1.36  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.47/1.36  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.47/1.36  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.47/1.36  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.47/1.36  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.47/1.36  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.47/1.36  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.47/1.36  tff(c_56, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.47/1.36  tff(c_69, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.47/1.36  tff(c_73, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_56, c_69])).
% 2.47/1.36  tff(c_102, plain, (![C_80, B_81, A_82]: (v5_relat_1(C_80, B_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.47/1.36  tff(c_106, plain, (v5_relat_1('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_102])).
% 2.47/1.36  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.47/1.36  tff(c_60, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.47/1.36  tff(c_54, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.47/1.36  tff(c_52, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.47/1.36  tff(c_58, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.47/1.36  tff(c_124, plain, (![A_89, B_90, C_91]: (k1_relset_1(A_89, B_90, C_91)=k1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.47/1.36  tff(c_128, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_56, c_124])).
% 2.47/1.36  tff(c_165, plain, (![B_112, A_113, C_114]: (k1_xboole_0=B_112 | k1_relset_1(A_113, B_112, C_114)=A_113 | ~v1_funct_2(C_114, A_113, B_112) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.47/1.36  tff(c_168, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_165])).
% 2.47/1.36  tff(c_171, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_128, c_168])).
% 2.47/1.36  tff(c_172, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_52, c_171])).
% 2.47/1.36  tff(c_133, plain, (![A_92, D_93]: (r2_hidden(k1_funct_1(A_92, D_93), k2_relat_1(A_92)) | ~r2_hidden(D_93, k1_relat_1(A_92)) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.47/1.36  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.47/1.36  tff(c_202, plain, (![A_121, D_122, B_123]: (r2_hidden(k1_funct_1(A_121, D_122), B_123) | ~r1_tarski(k2_relat_1(A_121), B_123) | ~r2_hidden(D_122, k1_relat_1(A_121)) | ~v1_funct_1(A_121) | ~v1_relat_1(A_121))), inference(resolution, [status(thm)], [c_133, c_2])).
% 2.47/1.36  tff(c_50, plain, (~r2_hidden(k1_funct_1('#skF_9', '#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.47/1.36  tff(c_207, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_7') | ~r2_hidden('#skF_8', k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_202, c_50])).
% 2.47/1.36  tff(c_214, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_60, c_54, c_172, c_207])).
% 2.47/1.36  tff(c_217, plain, (~v5_relat_1('#skF_9', '#skF_7') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_10, c_214])).
% 2.47/1.36  tff(c_221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_106, c_217])).
% 2.47/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.36  
% 2.47/1.36  Inference rules
% 2.47/1.36  ----------------------
% 2.47/1.36  #Ref     : 0
% 2.47/1.36  #Sup     : 36
% 2.47/1.36  #Fact    : 0
% 2.47/1.36  #Define  : 0
% 2.47/1.36  #Split   : 0
% 2.47/1.36  #Chain   : 0
% 2.47/1.36  #Close   : 0
% 2.47/1.36  
% 2.47/1.36  Ordering : KBO
% 2.47/1.36  
% 2.47/1.36  Simplification rules
% 2.47/1.36  ----------------------
% 2.47/1.36  #Subsume      : 3
% 2.47/1.36  #Demod        : 13
% 2.47/1.36  #Tautology    : 12
% 2.47/1.36  #SimpNegUnit  : 2
% 2.47/1.36  #BackRed      : 1
% 2.47/1.36  
% 2.47/1.36  #Partial instantiations: 0
% 2.47/1.36  #Strategies tried      : 1
% 2.47/1.36  
% 2.47/1.36  Timing (in seconds)
% 2.47/1.36  ----------------------
% 2.47/1.36  Preprocessing        : 0.34
% 2.47/1.36  Parsing              : 0.17
% 2.47/1.36  CNF conversion       : 0.03
% 2.47/1.36  Main loop            : 0.21
% 2.47/1.36  Inferencing          : 0.08
% 2.47/1.36  Reduction            : 0.06
% 2.47/1.36  Demodulation         : 0.04
% 2.47/1.36  BG Simplification    : 0.02
% 2.47/1.36  Subsumption          : 0.04
% 2.47/1.36  Abstraction          : 0.01
% 2.47/1.36  MUC search           : 0.00
% 2.47/1.36  Cooper               : 0.00
% 2.47/1.36  Total                : 0.57
% 2.47/1.36  Index Insertion      : 0.00
% 2.47/1.36  Index Deletion       : 0.00
% 2.47/1.36  Index Matching       : 0.00
% 2.47/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
