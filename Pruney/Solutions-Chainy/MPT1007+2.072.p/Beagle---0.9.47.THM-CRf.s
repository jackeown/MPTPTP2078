%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:21 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   61 (  71 expanded)
%              Number of leaves         :   34 (  41 expanded)
%              Depth                    :    6
%              Number of atoms          :   80 ( 118 expanded)
%              Number of equality atoms :   26 (  33 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_32,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_105,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_108,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_105])).

tff(c_111,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_108])).

tff(c_117,plain,(
    ! [C_53,B_54,A_55] :
      ( v5_relat_1(C_53,B_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_55,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_121,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_117])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_174,plain,(
    ! [B_75,C_76,A_77] :
      ( r2_hidden(k1_funct_1(B_75,C_76),A_77)
      | ~ r2_hidden(C_76,k1_relat_1(B_75))
      | ~ v1_funct_1(B_75)
      | ~ v5_relat_1(B_75,A_77)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_54,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_189,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_174,c_54])).

tff(c_195,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_121,c_62,c_189])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_60,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_122,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_relset_1(A_56,B_57,C_58) = k1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_126,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_122])).

tff(c_208,plain,(
    ! [B_84,A_85,C_86] :
      ( k1_xboole_0 = B_84
      | k1_relset_1(A_85,B_84,C_86) = A_85
      | ~ v1_funct_2(C_86,A_85,B_84)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_211,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_208])).

tff(c_214,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_126,c_211])).

tff(c_215,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_214])).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    ! [A_41,B_42] : k1_enumset1(A_41,A_41,B_42) = k2_tarski(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [E_7,B_2,C_3] : r2_hidden(E_7,k1_enumset1(E_7,B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_94,plain,(
    ! [A_43,B_44] : r2_hidden(A_43,k2_tarski(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_8])).

tff(c_97,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_94])).

tff(c_227,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_97])).

tff(c_231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:12:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.42  
% 2.21/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.42  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.21/1.42  
% 2.21/1.42  %Foreground sorts:
% 2.21/1.42  
% 2.21/1.42  
% 2.21/1.42  %Background operators:
% 2.21/1.42  
% 2.21/1.42  
% 2.21/1.42  %Foreground operators:
% 2.21/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.21/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.21/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.21/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.21/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.21/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.21/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.21/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.21/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.42  
% 2.44/1.43  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.44/1.43  tff(f_104, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 2.44/1.43  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.44/1.43  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.44/1.43  tff(f_64, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 2.44/1.43  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.44/1.43  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.44/1.43  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.44/1.43  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.44/1.43  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.44/1.43  tff(c_32, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.44/1.43  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.44/1.43  tff(c_105, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.44/1.43  tff(c_108, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_105])).
% 2.44/1.43  tff(c_111, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_108])).
% 2.44/1.43  tff(c_117, plain, (![C_53, B_54, A_55]: (v5_relat_1(C_53, B_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_55, B_54))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.44/1.43  tff(c_121, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_117])).
% 2.44/1.43  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.44/1.43  tff(c_174, plain, (![B_75, C_76, A_77]: (r2_hidden(k1_funct_1(B_75, C_76), A_77) | ~r2_hidden(C_76, k1_relat_1(B_75)) | ~v1_funct_1(B_75) | ~v5_relat_1(B_75, A_77) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.44/1.43  tff(c_54, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.44/1.43  tff(c_189, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_174, c_54])).
% 2.44/1.43  tff(c_195, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_121, c_62, c_189])).
% 2.44/1.43  tff(c_56, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.44/1.43  tff(c_60, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.44/1.43  tff(c_122, plain, (![A_56, B_57, C_58]: (k1_relset_1(A_56, B_57, C_58)=k1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.44/1.43  tff(c_126, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_122])).
% 2.44/1.43  tff(c_208, plain, (![B_84, A_85, C_86]: (k1_xboole_0=B_84 | k1_relset_1(A_85, B_84, C_86)=A_85 | ~v1_funct_2(C_86, A_85, B_84) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.44/1.43  tff(c_211, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_58, c_208])).
% 2.44/1.43  tff(c_214, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_126, c_211])).
% 2.44/1.43  tff(c_215, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_214])).
% 2.44/1.43  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.44/1.43  tff(c_76, plain, (![A_41, B_42]: (k1_enumset1(A_41, A_41, B_42)=k2_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.44/1.43  tff(c_8, plain, (![E_7, B_2, C_3]: (r2_hidden(E_7, k1_enumset1(E_7, B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.44/1.43  tff(c_94, plain, (![A_43, B_44]: (r2_hidden(A_43, k2_tarski(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_8])).
% 2.44/1.43  tff(c_97, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_94])).
% 2.44/1.43  tff(c_227, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_215, c_97])).
% 2.44/1.43  tff(c_231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195, c_227])).
% 2.44/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.43  
% 2.44/1.43  Inference rules
% 2.44/1.43  ----------------------
% 2.44/1.43  #Ref     : 0
% 2.44/1.43  #Sup     : 34
% 2.44/1.43  #Fact    : 0
% 2.44/1.43  #Define  : 0
% 2.44/1.43  #Split   : 0
% 2.44/1.43  #Chain   : 0
% 2.44/1.43  #Close   : 0
% 2.44/1.43  
% 2.44/1.43  Ordering : KBO
% 2.44/1.43  
% 2.44/1.43  Simplification rules
% 2.44/1.43  ----------------------
% 2.44/1.43  #Subsume      : 0
% 2.44/1.43  #Demod        : 14
% 2.44/1.43  #Tautology    : 16
% 2.44/1.43  #SimpNegUnit  : 3
% 2.44/1.43  #BackRed      : 4
% 2.44/1.43  
% 2.44/1.43  #Partial instantiations: 0
% 2.44/1.43  #Strategies tried      : 1
% 2.44/1.43  
% 2.44/1.43  Timing (in seconds)
% 2.44/1.43  ----------------------
% 2.44/1.44  Preprocessing        : 0.38
% 2.44/1.44  Parsing              : 0.20
% 2.44/1.44  CNF conversion       : 0.02
% 2.44/1.44  Main loop            : 0.19
% 2.44/1.44  Inferencing          : 0.07
% 2.44/1.44  Reduction            : 0.06
% 2.44/1.44  Demodulation         : 0.04
% 2.44/1.44  BG Simplification    : 0.02
% 2.44/1.44  Subsumption          : 0.04
% 2.44/1.44  Abstraction          : 0.01
% 2.44/1.44  MUC search           : 0.00
% 2.44/1.44  Cooper               : 0.00
% 2.44/1.44  Total                : 0.60
% 2.44/1.44  Index Insertion      : 0.00
% 2.44/1.44  Index Deletion       : 0.00
% 2.44/1.44  Index Matching       : 0.00
% 2.44/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
