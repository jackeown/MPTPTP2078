%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:04 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   64 (  83 expanded)
%              Number of leaves         :   36 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :   97 ( 166 expanded)
%              Number of equality atoms :   20 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
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
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_14,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_74,plain,(
    ! [B_69,A_70] :
      ( v1_relat_1(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_80,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_58,c_74])).

tff(c_84,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_80])).

tff(c_97,plain,(
    ! [C_75,B_76,A_77] :
      ( v5_relat_1(C_75,B_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_106,plain,(
    v5_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_97])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_62,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_56,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_60,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_164,plain,(
    ! [A_96,B_97,C_98] :
      ( k1_relset_1(A_96,B_97,C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_173,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_164])).

tff(c_294,plain,(
    ! [B_143,A_144,C_145] :
      ( k1_xboole_0 = B_143
      | k1_relset_1(A_144,B_143,C_145) = A_144
      | ~ v1_funct_2(C_145,A_144,B_143)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_144,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_301,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_294])).

tff(c_305,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_173,c_301])).

tff(c_306,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_305])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_209,plain,(
    ! [A_114,D_115] :
      ( r2_hidden(k1_funct_1(A_114,D_115),k2_relat_1(A_114))
      | ~ r2_hidden(D_115,k1_relat_1(A_114))
      | ~ v1_funct_1(A_114)
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_363,plain,(
    ! [A_159,D_160,A_161] :
      ( r2_hidden(k1_funct_1(A_159,D_160),A_161)
      | ~ m1_subset_1(k2_relat_1(A_159),k1_zfmisc_1(A_161))
      | ~ r2_hidden(D_160,k1_relat_1(A_159))
      | ~ v1_funct_1(A_159)
      | ~ v1_relat_1(A_159) ) ),
    inference(resolution,[status(thm)],[c_209,c_2])).

tff(c_368,plain,(
    ! [A_162,D_163,B_164] :
      ( r2_hidden(k1_funct_1(A_162,D_163),B_164)
      | ~ r2_hidden(D_163,k1_relat_1(A_162))
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162)
      | ~ r1_tarski(k2_relat_1(A_162),B_164) ) ),
    inference(resolution,[status(thm)],[c_6,c_363])).

tff(c_52,plain,(
    ~ r2_hidden(k1_funct_1('#skF_8','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_373,plain,
    ( ~ r2_hidden('#skF_7',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_368,c_52])).

tff(c_380,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_62,c_56,c_306,c_373])).

tff(c_383,plain,
    ( ~ v5_relat_1('#skF_8','#skF_6')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_380])).

tff(c_387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_106,c_383])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:24:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.35  
% 2.49/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.35  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.49/1.35  
% 2.49/1.35  %Foreground sorts:
% 2.49/1.35  
% 2.49/1.35  
% 2.49/1.35  %Background operators:
% 2.49/1.35  
% 2.49/1.35  
% 2.49/1.35  %Foreground operators:
% 2.49/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.49/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.49/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.49/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.49/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.49/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.49/1.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.49/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.49/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.49/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.49/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.49/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.35  
% 2.78/1.37  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.78/1.37  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.78/1.37  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.78/1.37  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.78/1.37  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.78/1.37  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.78/1.37  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.78/1.37  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.78/1.37  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.78/1.37  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.78/1.37  tff(c_14, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.78/1.37  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.78/1.37  tff(c_74, plain, (![B_69, A_70]: (v1_relat_1(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.37  tff(c_80, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_74])).
% 2.78/1.37  tff(c_84, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_80])).
% 2.78/1.37  tff(c_97, plain, (![C_75, B_76, A_77]: (v5_relat_1(C_75, B_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.78/1.37  tff(c_106, plain, (v5_relat_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_97])).
% 2.78/1.37  tff(c_12, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.78/1.37  tff(c_62, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.78/1.37  tff(c_56, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.78/1.37  tff(c_54, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.78/1.37  tff(c_60, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.78/1.37  tff(c_164, plain, (![A_96, B_97, C_98]: (k1_relset_1(A_96, B_97, C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.78/1.37  tff(c_173, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_164])).
% 2.78/1.37  tff(c_294, plain, (![B_143, A_144, C_145]: (k1_xboole_0=B_143 | k1_relset_1(A_144, B_143, C_145)=A_144 | ~v1_funct_2(C_145, A_144, B_143) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.78/1.37  tff(c_301, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_294])).
% 2.78/1.37  tff(c_305, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_173, c_301])).
% 2.78/1.37  tff(c_306, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_54, c_305])).
% 2.78/1.37  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.78/1.37  tff(c_209, plain, (![A_114, D_115]: (r2_hidden(k1_funct_1(A_114, D_115), k2_relat_1(A_114)) | ~r2_hidden(D_115, k1_relat_1(A_114)) | ~v1_funct_1(A_114) | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.78/1.37  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.78/1.37  tff(c_363, plain, (![A_159, D_160, A_161]: (r2_hidden(k1_funct_1(A_159, D_160), A_161) | ~m1_subset_1(k2_relat_1(A_159), k1_zfmisc_1(A_161)) | ~r2_hidden(D_160, k1_relat_1(A_159)) | ~v1_funct_1(A_159) | ~v1_relat_1(A_159))), inference(resolution, [status(thm)], [c_209, c_2])).
% 2.78/1.37  tff(c_368, plain, (![A_162, D_163, B_164]: (r2_hidden(k1_funct_1(A_162, D_163), B_164) | ~r2_hidden(D_163, k1_relat_1(A_162)) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162) | ~r1_tarski(k2_relat_1(A_162), B_164))), inference(resolution, [status(thm)], [c_6, c_363])).
% 2.78/1.37  tff(c_52, plain, (~r2_hidden(k1_funct_1('#skF_8', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.78/1.37  tff(c_373, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_368, c_52])).
% 2.78/1.37  tff(c_380, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_62, c_56, c_306, c_373])).
% 2.78/1.37  tff(c_383, plain, (~v5_relat_1('#skF_8', '#skF_6') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_12, c_380])).
% 2.78/1.37  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_106, c_383])).
% 2.78/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.37  
% 2.78/1.37  Inference rules
% 2.78/1.37  ----------------------
% 2.78/1.37  #Ref     : 0
% 2.78/1.37  #Sup     : 65
% 2.78/1.37  #Fact    : 0
% 2.78/1.37  #Define  : 0
% 2.78/1.37  #Split   : 2
% 2.78/1.37  #Chain   : 0
% 2.78/1.37  #Close   : 0
% 2.78/1.37  
% 2.78/1.37  Ordering : KBO
% 2.78/1.37  
% 2.78/1.37  Simplification rules
% 2.78/1.37  ----------------------
% 2.78/1.37  #Subsume      : 0
% 2.78/1.37  #Demod        : 26
% 2.78/1.37  #Tautology    : 18
% 2.78/1.37  #SimpNegUnit  : 4
% 2.78/1.37  #BackRed      : 1
% 2.78/1.37  
% 2.78/1.37  #Partial instantiations: 0
% 2.78/1.37  #Strategies tried      : 1
% 2.78/1.37  
% 2.78/1.37  Timing (in seconds)
% 2.78/1.37  ----------------------
% 2.78/1.37  Preprocessing        : 0.33
% 2.78/1.37  Parsing              : 0.17
% 2.78/1.37  CNF conversion       : 0.03
% 2.78/1.37  Main loop            : 0.26
% 2.78/1.37  Inferencing          : 0.10
% 2.78/1.37  Reduction            : 0.07
% 2.78/1.37  Demodulation         : 0.05
% 2.78/1.37  BG Simplification    : 0.02
% 2.78/1.37  Subsumption          : 0.05
% 2.78/1.37  Abstraction          : 0.01
% 2.78/1.37  MUC search           : 0.00
% 2.78/1.37  Cooper               : 0.00
% 2.78/1.37  Total                : 0.62
% 2.78/1.37  Index Insertion      : 0.00
% 2.78/1.37  Index Deletion       : 0.00
% 2.78/1.37  Index Matching       : 0.00
% 2.78/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
