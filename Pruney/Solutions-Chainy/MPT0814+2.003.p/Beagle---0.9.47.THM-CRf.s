%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:51 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   69 (  90 expanded)
%              Number of leaves         :   33 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  130 ( 190 expanded)
%              Number of equality atoms :   13 (  24 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ~ ( r2_hidden(A,D)
            & ! [E,F] :
                ~ ( A = k4_tarski(E,F)
                  & r2_hidden(E,B)
                  & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( v1_relat_1(D)
     => ( r2_hidden(k4_tarski(A,B),k5_relat_1(k6_relat_1(C),D))
      <=> ( r2_hidden(A,C)
          & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( v1_relat_1(D)
     => ( r2_hidden(k4_tarski(A,B),k5_relat_1(D,k6_relat_1(C)))
      <=> ( r2_hidden(B,C)
          & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_47,plain,(
    ! [C_41,A_42,B_43] :
      ( v4_relat_1(C_41,A_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_51,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_47])).

tff(c_41,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_45,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_41])).

tff(c_38,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_8,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_96,plain,(
    ! [A_64,B_65] :
      ( k5_relat_1(k6_relat_1(A_64),B_65) = B_65
      | ~ r1_tarski(k1_relat_1(B_65),A_64)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_100,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = B_11
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_134,plain,(
    ! [A_76,B_77,C_78] :
      ( k4_tarski('#skF_1'(A_76,B_77,C_78),'#skF_2'(A_76,B_77,C_78)) = A_76
      | ~ r2_hidden(A_76,k2_zfmisc_1(B_77,C_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_14,C_16,B_15,D_17] :
      ( r2_hidden(A_14,C_16)
      | ~ r2_hidden(k4_tarski(A_14,B_15),k5_relat_1(k6_relat_1(C_16),D_17))
      | ~ v1_relat_1(D_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_256,plain,(
    ! [C_115,A_116,D_114,B_113,C_117] :
      ( r2_hidden('#skF_1'(A_116,B_113,C_117),C_115)
      | ~ r2_hidden(A_116,k5_relat_1(k6_relat_1(C_115),D_114))
      | ~ v1_relat_1(D_114)
      | ~ r2_hidden(A_116,k2_zfmisc_1(B_113,C_117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_18])).

tff(c_348,plain,(
    ! [A_163,B_161,C_162,A_164,B_165] :
      ( r2_hidden('#skF_1'(A_163,B_165,C_162),A_164)
      | ~ r2_hidden(A_163,B_161)
      | ~ v1_relat_1(B_161)
      | ~ r2_hidden(A_163,k2_zfmisc_1(B_165,C_162))
      | ~ v4_relat_1(B_161,A_164)
      | ~ v1_relat_1(B_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_256])).

tff(c_358,plain,(
    ! [B_165,C_162,A_164] :
      ( r2_hidden('#skF_1'('#skF_3',B_165,C_162),A_164)
      | ~ r2_hidden('#skF_3',k2_zfmisc_1(B_165,C_162))
      | ~ v4_relat_1('#skF_6',A_164)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_38,c_348])).

tff(c_366,plain,(
    ! [B_166,C_167,A_168] :
      ( r2_hidden('#skF_1'('#skF_3',B_166,C_167),A_168)
      | ~ r2_hidden('#skF_3',k2_zfmisc_1(B_166,C_167))
      | ~ v4_relat_1('#skF_6',A_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_358])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( k4_tarski('#skF_1'(A_1,B_2,C_3),'#skF_2'(A_1,B_2,C_3)) = A_1
      | ~ r2_hidden(A_1,k2_zfmisc_1(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [C_50,B_51,A_52] :
      ( v5_relat_1(C_50,B_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_63,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_59])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78,plain,(
    ! [B_59,A_60] :
      ( k5_relat_1(B_59,k6_relat_1(A_60)) = B_59
      | ~ r1_tarski(k2_relat_1(B_59),A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_82,plain,(
    ! [B_13,A_12] :
      ( k5_relat_1(B_13,k6_relat_1(A_12)) = B_13
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(resolution,[status(thm)],[c_12,c_78])).

tff(c_24,plain,(
    ! [B_19,C_20,A_18,D_21] :
      ( r2_hidden(B_19,C_20)
      | ~ r2_hidden(k4_tarski(A_18,B_19),k5_relat_1(D_21,k6_relat_1(C_20)))
      | ~ v1_relat_1(D_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_269,plain,(
    ! [C_121,B_118,D_122,A_120,C_119] :
      ( r2_hidden('#skF_2'(A_120,B_118,C_121),C_119)
      | ~ r2_hidden(A_120,k5_relat_1(D_122,k6_relat_1(C_119)))
      | ~ v1_relat_1(D_122)
      | ~ r2_hidden(A_120,k2_zfmisc_1(B_118,C_121)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_24])).

tff(c_294,plain,(
    ! [C_143,A_141,B_142,B_139,A_140] :
      ( r2_hidden('#skF_2'(A_141,B_142,C_143),A_140)
      | ~ r2_hidden(A_141,B_139)
      | ~ v1_relat_1(B_139)
      | ~ r2_hidden(A_141,k2_zfmisc_1(B_142,C_143))
      | ~ v5_relat_1(B_139,A_140)
      | ~ v1_relat_1(B_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_269])).

tff(c_302,plain,(
    ! [B_142,C_143,A_140] :
      ( r2_hidden('#skF_2'('#skF_3',B_142,C_143),A_140)
      | ~ r2_hidden('#skF_3',k2_zfmisc_1(B_142,C_143))
      | ~ v5_relat_1('#skF_6',A_140)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_38,c_294])).

tff(c_309,plain,(
    ! [B_144,C_145,A_146] :
      ( r2_hidden('#skF_2'('#skF_3',B_144,C_145),A_146)
      | ~ r2_hidden('#skF_3',k2_zfmisc_1(B_144,C_145))
      | ~ v5_relat_1('#skF_6',A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_302])).

tff(c_36,plain,(
    ! [F_35,E_34] :
      ( ~ r2_hidden(F_35,'#skF_5')
      | ~ r2_hidden(E_34,'#skF_4')
      | k4_tarski(E_34,F_35) != '#skF_3' ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_322,plain,(
    ! [E_34,B_144,C_145] :
      ( ~ r2_hidden(E_34,'#skF_4')
      | k4_tarski(E_34,'#skF_2'('#skF_3',B_144,C_145)) != '#skF_3'
      | ~ r2_hidden('#skF_3',k2_zfmisc_1(B_144,C_145))
      | ~ v5_relat_1('#skF_6','#skF_5') ) ),
    inference(resolution,[status(thm)],[c_309,c_36])).

tff(c_330,plain,(
    ! [E_147,B_148,C_149] :
      ( ~ r2_hidden(E_147,'#skF_4')
      | k4_tarski(E_147,'#skF_2'('#skF_3',B_148,C_149)) != '#skF_3'
      | ~ r2_hidden('#skF_3',k2_zfmisc_1(B_148,C_149)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_322])).

tff(c_334,plain,(
    ! [B_2,C_3] :
      ( ~ r2_hidden('#skF_1'('#skF_3',B_2,C_3),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_zfmisc_1(B_2,C_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_330])).

tff(c_372,plain,(
    ! [B_166,C_167] :
      ( ~ r2_hidden('#skF_3',k2_zfmisc_1(B_166,C_167))
      | ~ v4_relat_1('#skF_6','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_366,c_334])).

tff(c_389,plain,(
    ! [B_166,C_167] : ~ r2_hidden('#skF_3',k2_zfmisc_1(B_166,C_167)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_372])).

tff(c_69,plain,(
    ! [C_55,A_56,B_57] :
      ( r2_hidden(C_55,A_56)
      | ~ r2_hidden(C_55,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,(
    ! [A_58] :
      ( r2_hidden('#skF_3',A_58)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_58)) ) ),
    inference(resolution,[status(thm)],[c_38,c_69])).

tff(c_77,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_73])).

tff(c_396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:43:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.37  
% 2.77/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.37  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.77/1.37  
% 2.77/1.37  %Foreground sorts:
% 2.77/1.37  
% 2.77/1.37  
% 2.77/1.37  %Background operators:
% 2.77/1.37  
% 2.77/1.37  
% 2.77/1.37  %Foreground operators:
% 2.77/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.77/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.77/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.77/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.77/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.77/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.77/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.77/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.77/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.77/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.37  
% 2.77/1.39  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 2.77/1.39  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.77/1.39  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.77/1.39  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.77/1.39  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.77/1.39  tff(f_32, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 2.77/1.39  tff(f_59, axiom, (![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(k6_relat_1(C), D)) <=> (r2_hidden(A, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_relat_1)).
% 2.77/1.39  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.77/1.39  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.77/1.39  tff(f_67, axiom, (![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(D, k6_relat_1(C))) <=> (r2_hidden(B, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_relat_1)).
% 2.77/1.39  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.77/1.39  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.77/1.39  tff(c_47, plain, (![C_41, A_42, B_43]: (v4_relat_1(C_41, A_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.77/1.39  tff(c_51, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_47])).
% 2.77/1.39  tff(c_41, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.77/1.39  tff(c_45, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_41])).
% 2.77/1.39  tff(c_38, plain, (r2_hidden('#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.77/1.39  tff(c_8, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(B_11), A_10) | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.77/1.39  tff(c_96, plain, (![A_64, B_65]: (k5_relat_1(k6_relat_1(A_64), B_65)=B_65 | ~r1_tarski(k1_relat_1(B_65), A_64) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.77/1.39  tff(c_100, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=B_11 | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_8, c_96])).
% 2.77/1.39  tff(c_134, plain, (![A_76, B_77, C_78]: (k4_tarski('#skF_1'(A_76, B_77, C_78), '#skF_2'(A_76, B_77, C_78))=A_76 | ~r2_hidden(A_76, k2_zfmisc_1(B_77, C_78)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.39  tff(c_18, plain, (![A_14, C_16, B_15, D_17]: (r2_hidden(A_14, C_16) | ~r2_hidden(k4_tarski(A_14, B_15), k5_relat_1(k6_relat_1(C_16), D_17)) | ~v1_relat_1(D_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.77/1.39  tff(c_256, plain, (![C_115, A_116, D_114, B_113, C_117]: (r2_hidden('#skF_1'(A_116, B_113, C_117), C_115) | ~r2_hidden(A_116, k5_relat_1(k6_relat_1(C_115), D_114)) | ~v1_relat_1(D_114) | ~r2_hidden(A_116, k2_zfmisc_1(B_113, C_117)))), inference(superposition, [status(thm), theory('equality')], [c_134, c_18])).
% 2.77/1.39  tff(c_348, plain, (![A_163, B_161, C_162, A_164, B_165]: (r2_hidden('#skF_1'(A_163, B_165, C_162), A_164) | ~r2_hidden(A_163, B_161) | ~v1_relat_1(B_161) | ~r2_hidden(A_163, k2_zfmisc_1(B_165, C_162)) | ~v4_relat_1(B_161, A_164) | ~v1_relat_1(B_161))), inference(superposition, [status(thm), theory('equality')], [c_100, c_256])).
% 2.77/1.39  tff(c_358, plain, (![B_165, C_162, A_164]: (r2_hidden('#skF_1'('#skF_3', B_165, C_162), A_164) | ~r2_hidden('#skF_3', k2_zfmisc_1(B_165, C_162)) | ~v4_relat_1('#skF_6', A_164) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_38, c_348])).
% 2.77/1.39  tff(c_366, plain, (![B_166, C_167, A_168]: (r2_hidden('#skF_1'('#skF_3', B_166, C_167), A_168) | ~r2_hidden('#skF_3', k2_zfmisc_1(B_166, C_167)) | ~v4_relat_1('#skF_6', A_168))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_358])).
% 2.77/1.39  tff(c_2, plain, (![A_1, B_2, C_3]: (k4_tarski('#skF_1'(A_1, B_2, C_3), '#skF_2'(A_1, B_2, C_3))=A_1 | ~r2_hidden(A_1, k2_zfmisc_1(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.39  tff(c_59, plain, (![C_50, B_51, A_52]: (v5_relat_1(C_50, B_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.77/1.39  tff(c_63, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_59])).
% 2.77/1.39  tff(c_12, plain, (![B_13, A_12]: (r1_tarski(k2_relat_1(B_13), A_12) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.77/1.39  tff(c_78, plain, (![B_59, A_60]: (k5_relat_1(B_59, k6_relat_1(A_60))=B_59 | ~r1_tarski(k2_relat_1(B_59), A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.77/1.39  tff(c_82, plain, (![B_13, A_12]: (k5_relat_1(B_13, k6_relat_1(A_12))=B_13 | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(resolution, [status(thm)], [c_12, c_78])).
% 2.77/1.39  tff(c_24, plain, (![B_19, C_20, A_18, D_21]: (r2_hidden(B_19, C_20) | ~r2_hidden(k4_tarski(A_18, B_19), k5_relat_1(D_21, k6_relat_1(C_20))) | ~v1_relat_1(D_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.77/1.39  tff(c_269, plain, (![C_121, B_118, D_122, A_120, C_119]: (r2_hidden('#skF_2'(A_120, B_118, C_121), C_119) | ~r2_hidden(A_120, k5_relat_1(D_122, k6_relat_1(C_119))) | ~v1_relat_1(D_122) | ~r2_hidden(A_120, k2_zfmisc_1(B_118, C_121)))), inference(superposition, [status(thm), theory('equality')], [c_134, c_24])).
% 2.77/1.39  tff(c_294, plain, (![C_143, A_141, B_142, B_139, A_140]: (r2_hidden('#skF_2'(A_141, B_142, C_143), A_140) | ~r2_hidden(A_141, B_139) | ~v1_relat_1(B_139) | ~r2_hidden(A_141, k2_zfmisc_1(B_142, C_143)) | ~v5_relat_1(B_139, A_140) | ~v1_relat_1(B_139))), inference(superposition, [status(thm), theory('equality')], [c_82, c_269])).
% 2.77/1.39  tff(c_302, plain, (![B_142, C_143, A_140]: (r2_hidden('#skF_2'('#skF_3', B_142, C_143), A_140) | ~r2_hidden('#skF_3', k2_zfmisc_1(B_142, C_143)) | ~v5_relat_1('#skF_6', A_140) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_38, c_294])).
% 2.77/1.39  tff(c_309, plain, (![B_144, C_145, A_146]: (r2_hidden('#skF_2'('#skF_3', B_144, C_145), A_146) | ~r2_hidden('#skF_3', k2_zfmisc_1(B_144, C_145)) | ~v5_relat_1('#skF_6', A_146))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_302])).
% 2.77/1.39  tff(c_36, plain, (![F_35, E_34]: (~r2_hidden(F_35, '#skF_5') | ~r2_hidden(E_34, '#skF_4') | k4_tarski(E_34, F_35)!='#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.77/1.39  tff(c_322, plain, (![E_34, B_144, C_145]: (~r2_hidden(E_34, '#skF_4') | k4_tarski(E_34, '#skF_2'('#skF_3', B_144, C_145))!='#skF_3' | ~r2_hidden('#skF_3', k2_zfmisc_1(B_144, C_145)) | ~v5_relat_1('#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_309, c_36])).
% 2.77/1.39  tff(c_330, plain, (![E_147, B_148, C_149]: (~r2_hidden(E_147, '#skF_4') | k4_tarski(E_147, '#skF_2'('#skF_3', B_148, C_149))!='#skF_3' | ~r2_hidden('#skF_3', k2_zfmisc_1(B_148, C_149)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_322])).
% 2.77/1.39  tff(c_334, plain, (![B_2, C_3]: (~r2_hidden('#skF_1'('#skF_3', B_2, C_3), '#skF_4') | ~r2_hidden('#skF_3', k2_zfmisc_1(B_2, C_3)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_330])).
% 2.77/1.39  tff(c_372, plain, (![B_166, C_167]: (~r2_hidden('#skF_3', k2_zfmisc_1(B_166, C_167)) | ~v4_relat_1('#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_366, c_334])).
% 2.77/1.39  tff(c_389, plain, (![B_166, C_167]: (~r2_hidden('#skF_3', k2_zfmisc_1(B_166, C_167)))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_372])).
% 2.77/1.39  tff(c_69, plain, (![C_55, A_56, B_57]: (r2_hidden(C_55, A_56) | ~r2_hidden(C_55, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.39  tff(c_73, plain, (![A_58]: (r2_hidden('#skF_3', A_58) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_58)))), inference(resolution, [status(thm)], [c_38, c_69])).
% 2.77/1.39  tff(c_77, plain, (r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_73])).
% 2.77/1.39  tff(c_396, plain, $false, inference(negUnitSimplification, [status(thm)], [c_389, c_77])).
% 2.77/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.39  
% 2.77/1.39  Inference rules
% 2.77/1.39  ----------------------
% 2.77/1.39  #Ref     : 0
% 2.77/1.39  #Sup     : 89
% 2.77/1.39  #Fact    : 0
% 2.77/1.39  #Define  : 0
% 2.77/1.39  #Split   : 2
% 2.77/1.39  #Chain   : 0
% 2.77/1.39  #Close   : 0
% 2.77/1.39  
% 2.77/1.39  Ordering : KBO
% 2.77/1.39  
% 2.77/1.39  Simplification rules
% 2.77/1.39  ----------------------
% 2.77/1.39  #Subsume      : 8
% 2.77/1.39  #Demod        : 4
% 2.77/1.39  #Tautology    : 16
% 2.77/1.39  #SimpNegUnit  : 1
% 2.77/1.39  #BackRed      : 1
% 2.77/1.39  
% 2.77/1.39  #Partial instantiations: 0
% 2.77/1.39  #Strategies tried      : 1
% 2.77/1.39  
% 2.77/1.39  Timing (in seconds)
% 2.77/1.39  ----------------------
% 2.77/1.39  Preprocessing        : 0.31
% 2.77/1.39  Parsing              : 0.18
% 2.77/1.39  CNF conversion       : 0.02
% 2.77/1.39  Main loop            : 0.30
% 2.77/1.39  Inferencing          : 0.12
% 2.77/1.39  Reduction            : 0.07
% 2.77/1.39  Demodulation         : 0.05
% 2.77/1.39  BG Simplification    : 0.02
% 2.77/1.39  Subsumption          : 0.07
% 2.77/1.39  Abstraction          : 0.01
% 2.77/1.39  MUC search           : 0.00
% 2.77/1.39  Cooper               : 0.00
% 2.77/1.39  Total                : 0.64
% 2.77/1.39  Index Insertion      : 0.00
% 2.77/1.39  Index Deletion       : 0.00
% 2.77/1.39  Index Matching       : 0.00
% 2.77/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
