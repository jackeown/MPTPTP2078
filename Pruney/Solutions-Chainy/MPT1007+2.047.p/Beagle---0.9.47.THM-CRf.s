%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:17 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   73 (  83 expanded)
%              Number of leaves         :   42 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :   93 ( 131 expanded)
%              Number of equality atoms :   32 (  39 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
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

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

tff(c_80,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_104,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_108,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_104])).

tff(c_84,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_127,plain,(
    ! [C_93,B_94,A_95] :
      ( v5_relat_1(C_93,B_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_131,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_127])).

tff(c_218,plain,(
    ! [B_144,A_145] :
      ( r2_hidden(k1_funct_1(B_144,A_145),k2_relat_1(B_144))
      | ~ r2_hidden(A_145,k1_relat_1(B_144))
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_52,plain,(
    ! [C_41,A_38,B_39] :
      ( r2_hidden(C_41,A_38)
      | ~ r2_hidden(C_41,k2_relat_1(B_39))
      | ~ v5_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_233,plain,(
    ! [B_156,A_157,A_158] :
      ( r2_hidden(k1_funct_1(B_156,A_157),A_158)
      | ~ v5_relat_1(B_156,A_158)
      | ~ r2_hidden(A_157,k1_relat_1(B_156))
      | ~ v1_funct_1(B_156)
      | ~ v1_relat_1(B_156) ) ),
    inference(resolution,[status(thm)],[c_218,c_52])).

tff(c_76,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_239,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_233,c_76])).

tff(c_243,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_84,c_131,c_239])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_82,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_199,plain,(
    ! [A_134,B_135,C_136] :
      ( k1_relset_1(A_134,B_135,C_136) = k1_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_203,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_199])).

tff(c_244,plain,(
    ! [B_159,A_160,C_161] :
      ( k1_xboole_0 = B_159
      | k1_relset_1(A_160,B_159,C_161) = A_160
      | ~ v1_funct_2(C_161,A_160,B_159)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_247,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_244])).

tff(c_250,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_203,c_247])).

tff(c_251,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_250])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    ! [A_96,B_97,C_98,D_99] : k3_enumset1(A_96,A_96,B_97,C_98,D_99) = k2_enumset1(A_96,B_97,C_98,D_99) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_29,G_37,D_32,C_31,B_30] : r2_hidden(G_37,k3_enumset1(A_29,B_30,C_31,D_32,G_37)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_156,plain,(
    ! [D_100,A_101,B_102,C_103] : r2_hidden(D_100,k2_enumset1(A_101,B_102,C_103,D_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_18])).

tff(c_160,plain,(
    ! [C_104,A_105,B_106] : r2_hidden(C_104,k1_enumset1(A_105,B_106,C_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_156])).

tff(c_164,plain,(
    ! [B_107,A_108] : r2_hidden(B_107,k2_tarski(A_108,B_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_160])).

tff(c_167,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_164])).

tff(c_259,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_167])).

tff(c_263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_259])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.36  
% 2.49/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.36  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.49/1.36  
% 2.49/1.36  %Foreground sorts:
% 2.49/1.36  
% 2.49/1.36  
% 2.49/1.36  %Background operators:
% 2.49/1.36  
% 2.49/1.36  
% 2.49/1.36  %Foreground operators:
% 2.49/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.49/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.49/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.49/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.49/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.49/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.49/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.49/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.36  
% 2.69/1.37  tff(f_121, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 2.69/1.37  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.69/1.37  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.69/1.37  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.69/1.37  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 2.69/1.37  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.69/1.37  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.69/1.37  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.69/1.37  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.69/1.37  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.69/1.37  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.69/1.37  tff(f_60, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 2.69/1.37  tff(c_80, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.69/1.37  tff(c_104, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.69/1.37  tff(c_108, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_80, c_104])).
% 2.69/1.37  tff(c_84, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.69/1.37  tff(c_127, plain, (![C_93, B_94, A_95]: (v5_relat_1(C_93, B_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.69/1.37  tff(c_131, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_127])).
% 2.69/1.37  tff(c_218, plain, (![B_144, A_145]: (r2_hidden(k1_funct_1(B_144, A_145), k2_relat_1(B_144)) | ~r2_hidden(A_145, k1_relat_1(B_144)) | ~v1_funct_1(B_144) | ~v1_relat_1(B_144))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.69/1.37  tff(c_52, plain, (![C_41, A_38, B_39]: (r2_hidden(C_41, A_38) | ~r2_hidden(C_41, k2_relat_1(B_39)) | ~v5_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.69/1.37  tff(c_233, plain, (![B_156, A_157, A_158]: (r2_hidden(k1_funct_1(B_156, A_157), A_158) | ~v5_relat_1(B_156, A_158) | ~r2_hidden(A_157, k1_relat_1(B_156)) | ~v1_funct_1(B_156) | ~v1_relat_1(B_156))), inference(resolution, [status(thm)], [c_218, c_52])).
% 2.69/1.37  tff(c_76, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.69/1.37  tff(c_239, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_233, c_76])).
% 2.69/1.37  tff(c_243, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_84, c_131, c_239])).
% 2.69/1.37  tff(c_78, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.69/1.37  tff(c_82, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.69/1.37  tff(c_199, plain, (![A_134, B_135, C_136]: (k1_relset_1(A_134, B_135, C_136)=k1_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.69/1.37  tff(c_203, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_80, c_199])).
% 2.69/1.37  tff(c_244, plain, (![B_159, A_160, C_161]: (k1_xboole_0=B_159 | k1_relset_1(A_160, B_159, C_161)=A_160 | ~v1_funct_2(C_161, A_160, B_159) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.69/1.37  tff(c_247, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_80, c_244])).
% 2.69/1.37  tff(c_250, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_203, c_247])).
% 2.69/1.37  tff(c_251, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_78, c_250])).
% 2.69/1.37  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.69/1.37  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.37  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.37  tff(c_132, plain, (![A_96, B_97, C_98, D_99]: (k3_enumset1(A_96, A_96, B_97, C_98, D_99)=k2_enumset1(A_96, B_97, C_98, D_99))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.69/1.37  tff(c_18, plain, (![A_29, G_37, D_32, C_31, B_30]: (r2_hidden(G_37, k3_enumset1(A_29, B_30, C_31, D_32, G_37)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.69/1.37  tff(c_156, plain, (![D_100, A_101, B_102, C_103]: (r2_hidden(D_100, k2_enumset1(A_101, B_102, C_103, D_100)))), inference(superposition, [status(thm), theory('equality')], [c_132, c_18])).
% 2.69/1.37  tff(c_160, plain, (![C_104, A_105, B_106]: (r2_hidden(C_104, k1_enumset1(A_105, B_106, C_104)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_156])).
% 2.69/1.37  tff(c_164, plain, (![B_107, A_108]: (r2_hidden(B_107, k2_tarski(A_108, B_107)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_160])).
% 2.69/1.37  tff(c_167, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_164])).
% 2.69/1.37  tff(c_259, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_251, c_167])).
% 2.69/1.37  tff(c_263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_243, c_259])).
% 2.69/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.37  
% 2.69/1.37  Inference rules
% 2.69/1.37  ----------------------
% 2.69/1.37  #Ref     : 0
% 2.69/1.37  #Sup     : 39
% 2.69/1.37  #Fact    : 0
% 2.69/1.37  #Define  : 0
% 2.69/1.37  #Split   : 0
% 2.69/1.37  #Chain   : 0
% 2.69/1.37  #Close   : 0
% 2.69/1.37  
% 2.69/1.37  Ordering : KBO
% 2.69/1.37  
% 2.69/1.37  Simplification rules
% 2.69/1.37  ----------------------
% 2.69/1.37  #Subsume      : 0
% 2.69/1.37  #Demod        : 13
% 2.69/1.37  #Tautology    : 19
% 2.69/1.37  #SimpNegUnit  : 2
% 2.69/1.37  #BackRed      : 4
% 2.69/1.37  
% 2.69/1.37  #Partial instantiations: 0
% 2.69/1.37  #Strategies tried      : 1
% 2.69/1.37  
% 2.69/1.37  Timing (in seconds)
% 2.69/1.37  ----------------------
% 2.69/1.38  Preprocessing        : 0.37
% 2.69/1.38  Parsing              : 0.18
% 2.69/1.38  CNF conversion       : 0.03
% 2.69/1.38  Main loop            : 0.22
% 2.69/1.38  Inferencing          : 0.07
% 2.69/1.38  Reduction            : 0.07
% 2.69/1.38  Demodulation         : 0.05
% 2.69/1.38  BG Simplification    : 0.02
% 2.69/1.38  Subsumption          : 0.05
% 2.69/1.38  Abstraction          : 0.01
% 2.69/1.38  MUC search           : 0.00
% 2.69/1.38  Cooper               : 0.00
% 2.69/1.38  Total                : 0.63
% 2.69/1.38  Index Insertion      : 0.00
% 2.69/1.38  Index Deletion       : 0.00
% 2.69/1.38  Index Matching       : 0.00
% 2.69/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
