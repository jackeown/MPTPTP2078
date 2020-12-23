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
% DateTime   : Thu Dec  3 10:14:41 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 111 expanded)
%              Number of leaves         :   43 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 198 expanded)
%              Number of equality atoms :   45 (  86 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_1)).

tff(c_80,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_162,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_166,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_162])).

tff(c_76,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_194,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_76])).

tff(c_54,plain,(
    ! [A_41,B_42] : v1_relat_1(k2_zfmisc_1(A_41,B_42)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_118,plain,(
    ! [B_86,A_87] :
      ( v1_relat_1(B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_87))
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_121,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_118])).

tff(c_124,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_121])).

tff(c_84,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_82,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_184,plain,(
    ! [A_115,B_116,C_117] :
      ( k1_relset_1(A_115,B_116,C_117) = k1_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_188,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_184])).

tff(c_265,plain,(
    ! [B_161,A_162,C_163] :
      ( k1_xboole_0 = B_161
      | k1_relset_1(A_162,B_161,C_163) = A_162
      | ~ v1_funct_2(C_163,A_162,B_161)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_162,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_268,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_265])).

tff(c_271,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_188,c_268])).

tff(c_272,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_271])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    ! [A_91,B_92,C_93,D_94] : k3_enumset1(A_91,A_91,B_92,C_93,D_94) = k2_enumset1(A_91,B_92,C_93,D_94) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [E_33,G_37,D_32,C_31,B_30] : r2_hidden(G_37,k3_enumset1(G_37,B_30,C_31,D_32,E_33)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_158,plain,(
    ! [A_95,B_96,C_97,D_98] : r2_hidden(A_95,k2_enumset1(A_95,B_96,C_97,D_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_26])).

tff(c_167,plain,(
    ! [A_102,B_103,C_104] : r2_hidden(A_102,k1_enumset1(A_102,B_103,C_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_158])).

tff(c_171,plain,(
    ! [A_105,B_106] : r2_hidden(A_105,k2_tarski(A_105,B_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_167])).

tff(c_174,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_171])).

tff(c_283,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_174])).

tff(c_56,plain,(
    ! [A_43] :
      ( k7_relat_1(A_43,k1_relat_1(A_43)) = A_43
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_58,plain,(
    ! [B_45,A_44] :
      ( k2_relat_1(k7_relat_1(B_45,k1_tarski(A_44))) = k1_tarski(k1_funct_1(B_45,A_44))
      | ~ r2_hidden(A_44,k1_relat_1(B_45))
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_427,plain,(
    ! [B_191] :
      ( k2_relat_1(k7_relat_1(B_191,k1_relat_1('#skF_5'))) = k1_tarski(k1_funct_1(B_191,'#skF_3'))
      | ~ r2_hidden('#skF_3',k1_relat_1(B_191))
      | ~ v1_funct_1(B_191)
      | ~ v1_relat_1(B_191) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_58])).

tff(c_437,plain,
    ( k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k2_relat_1('#skF_5')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_427])).

tff(c_441,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_124,c_84,c_283,c_437])).

tff(c_443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:45:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.39  
% 2.79/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.39  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.79/1.39  
% 2.79/1.39  %Foreground sorts:
% 2.79/1.39  
% 2.79/1.39  
% 2.79/1.39  %Background operators:
% 2.79/1.39  
% 2.79/1.39  
% 2.79/1.39  %Foreground operators:
% 2.79/1.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.79/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.79/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 2.79/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 2.79/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.79/1.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.79/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.79/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.79/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.79/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.79/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.79/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.79/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.79/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.79/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.79/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.79/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.79/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.79/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.79/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.39  
% 2.79/1.41  tff(f_119, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 2.79/1.41  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.79/1.41  tff(f_69, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.79/1.41  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.79/1.41  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.79/1.41  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.79/1.41  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.79/1.41  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.79/1.41  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.79/1.41  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.79/1.41  tff(f_60, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 2.79/1.41  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.79/1.41  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_funct_1)).
% 2.79/1.41  tff(c_80, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.79/1.41  tff(c_162, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.79/1.41  tff(c_166, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_80, c_162])).
% 2.79/1.41  tff(c_76, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.79/1.41  tff(c_194, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_76])).
% 2.79/1.41  tff(c_54, plain, (![A_41, B_42]: (v1_relat_1(k2_zfmisc_1(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.79/1.41  tff(c_118, plain, (![B_86, A_87]: (v1_relat_1(B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_87)) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.79/1.41  tff(c_121, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_118])).
% 2.79/1.41  tff(c_124, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_121])).
% 2.79/1.41  tff(c_84, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.79/1.41  tff(c_78, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.79/1.41  tff(c_82, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.79/1.41  tff(c_184, plain, (![A_115, B_116, C_117]: (k1_relset_1(A_115, B_116, C_117)=k1_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.79/1.41  tff(c_188, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_80, c_184])).
% 2.79/1.41  tff(c_265, plain, (![B_161, A_162, C_163]: (k1_xboole_0=B_161 | k1_relset_1(A_162, B_161, C_163)=A_162 | ~v1_funct_2(C_163, A_162, B_161) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_162, B_161))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.79/1.41  tff(c_268, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_80, c_265])).
% 2.79/1.41  tff(c_271, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_188, c_268])).
% 2.79/1.41  tff(c_272, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_78, c_271])).
% 2.79/1.41  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.79/1.41  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.79/1.41  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.79/1.41  tff(c_134, plain, (![A_91, B_92, C_93, D_94]: (k3_enumset1(A_91, A_91, B_92, C_93, D_94)=k2_enumset1(A_91, B_92, C_93, D_94))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.79/1.41  tff(c_26, plain, (![E_33, G_37, D_32, C_31, B_30]: (r2_hidden(G_37, k3_enumset1(G_37, B_30, C_31, D_32, E_33)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.79/1.41  tff(c_158, plain, (![A_95, B_96, C_97, D_98]: (r2_hidden(A_95, k2_enumset1(A_95, B_96, C_97, D_98)))), inference(superposition, [status(thm), theory('equality')], [c_134, c_26])).
% 2.79/1.41  tff(c_167, plain, (![A_102, B_103, C_104]: (r2_hidden(A_102, k1_enumset1(A_102, B_103, C_104)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_158])).
% 2.79/1.41  tff(c_171, plain, (![A_105, B_106]: (r2_hidden(A_105, k2_tarski(A_105, B_106)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_167])).
% 2.79/1.41  tff(c_174, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_171])).
% 2.79/1.41  tff(c_283, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_272, c_174])).
% 2.79/1.41  tff(c_56, plain, (![A_43]: (k7_relat_1(A_43, k1_relat_1(A_43))=A_43 | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.79/1.41  tff(c_58, plain, (![B_45, A_44]: (k2_relat_1(k7_relat_1(B_45, k1_tarski(A_44)))=k1_tarski(k1_funct_1(B_45, A_44)) | ~r2_hidden(A_44, k1_relat_1(B_45)) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.79/1.41  tff(c_427, plain, (![B_191]: (k2_relat_1(k7_relat_1(B_191, k1_relat_1('#skF_5')))=k1_tarski(k1_funct_1(B_191, '#skF_3')) | ~r2_hidden('#skF_3', k1_relat_1(B_191)) | ~v1_funct_1(B_191) | ~v1_relat_1(B_191))), inference(superposition, [status(thm), theory('equality')], [c_272, c_58])).
% 2.79/1.41  tff(c_437, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k2_relat_1('#skF_5') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_56, c_427])).
% 2.79/1.41  tff(c_441, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_124, c_84, c_283, c_437])).
% 2.79/1.41  tff(c_443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_441])).
% 2.79/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.41  
% 2.79/1.41  Inference rules
% 2.79/1.41  ----------------------
% 2.79/1.41  #Ref     : 0
% 2.79/1.41  #Sup     : 78
% 2.79/1.41  #Fact    : 0
% 2.79/1.41  #Define  : 0
% 2.79/1.41  #Split   : 0
% 2.79/1.41  #Chain   : 0
% 2.79/1.41  #Close   : 0
% 2.79/1.41  
% 2.79/1.41  Ordering : KBO
% 2.79/1.41  
% 2.79/1.41  Simplification rules
% 2.79/1.41  ----------------------
% 2.79/1.41  #Subsume      : 0
% 2.79/1.41  #Demod        : 25
% 2.79/1.41  #Tautology    : 56
% 2.79/1.41  #SimpNegUnit  : 5
% 2.79/1.41  #BackRed      : 5
% 2.79/1.41  
% 2.79/1.41  #Partial instantiations: 0
% 2.79/1.41  #Strategies tried      : 1
% 2.79/1.41  
% 2.79/1.41  Timing (in seconds)
% 2.79/1.41  ----------------------
% 2.79/1.41  Preprocessing        : 0.36
% 2.79/1.41  Parsing              : 0.18
% 2.79/1.41  CNF conversion       : 0.02
% 2.79/1.41  Main loop            : 0.27
% 2.79/1.41  Inferencing          : 0.09
% 2.79/1.41  Reduction            : 0.08
% 2.79/1.41  Demodulation         : 0.06
% 2.79/1.41  BG Simplification    : 0.02
% 2.79/1.41  Subsumption          : 0.06
% 2.79/1.41  Abstraction          : 0.02
% 2.79/1.41  MUC search           : 0.00
% 2.79/1.41  Cooper               : 0.00
% 2.79/1.41  Total                : 0.65
% 2.79/1.41  Index Insertion      : 0.00
% 2.79/1.41  Index Deletion       : 0.00
% 2.79/1.41  Index Matching       : 0.00
% 2.79/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
