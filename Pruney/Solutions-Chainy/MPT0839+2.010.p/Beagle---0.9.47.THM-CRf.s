%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:23 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 111 expanded)
%              Number of leaves         :   34 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   92 ( 205 expanded)
%              Number of equality atoms :   27 (  56 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_40,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_78,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_92,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_78])).

tff(c_26,plain,(
    ! [A_15] :
      ( k2_relat_1(A_15) = k1_xboole_0
      | k1_relat_1(A_15) != k1_xboole_0
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_99,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92,c_26])).

tff(c_102,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_122,plain,(
    ! [C_64,A_65,B_66] :
      ( v4_relat_1(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_136,plain,(
    v4_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_122])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    ! [C_44,A_45] :
      ( r2_hidden(C_44,k1_zfmisc_1(A_45))
      | ~ r1_tarski(C_44,A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_58,plain,(
    ! [C_44,A_45] :
      ( m1_subset_1(C_44,k1_zfmisc_1(A_45))
      | ~ r1_tarski(C_44,A_45) ) ),
    inference(resolution,[status(thm)],[c_54,c_16])).

tff(c_163,plain,(
    ! [A_73,C_74,B_75] :
      ( m1_subset_1(A_73,C_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(C_74))
      | ~ r2_hidden(A_73,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_186,plain,(
    ! [A_80,A_81,C_82] :
      ( m1_subset_1(A_80,A_81)
      | ~ r2_hidden(A_80,C_82)
      | ~ r1_tarski(C_82,A_81) ) ),
    inference(resolution,[status(thm)],[c_58,c_163])).

tff(c_192,plain,(
    ! [A_1,A_81] :
      ( m1_subset_1('#skF_1'(A_1),A_81)
      | ~ r1_tarski(A_1,A_81)
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_2,c_186])).

tff(c_218,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_relset_1(A_88,B_89,C_90) = k1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_237,plain,(
    k1_relset_1('#skF_5','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_218])).

tff(c_69,plain,(
    ! [D_48] :
      ( ~ r2_hidden(D_48,k1_relset_1('#skF_5','#skF_4','#skF_6'))
      | ~ m1_subset_1(D_48,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_5','#skF_4','#skF_6')),'#skF_5')
    | k1_relset_1('#skF_5','#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_69])).

tff(c_104,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_5','#skF_4','#skF_6')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_238,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_104])).

tff(c_246,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_192,c_238])).

tff(c_249,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_246])).

tff(c_252,plain,
    ( ~ v4_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_249])).

tff(c_256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_136,c_252])).

tff(c_257,plain,(
    k1_relset_1('#skF_5','#skF_4','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_407,plain,(
    ! [A_128,B_129,C_130] :
      ( k1_relset_1(A_128,B_129,C_130) = k1_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_422,plain,(
    k1_relset_1('#skF_5','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_407])).

tff(c_427,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_422])).

tff(c_429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_427])).

tff(c_430,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_611,plain,(
    ! [A_164,B_165,C_166] :
      ( k2_relset_1(A_164,B_165,C_166) = k2_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_626,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_611])).

tff(c_631,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_626])).

tff(c_633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_631])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:22:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.66  
% 2.98/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.66  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.98/1.66  
% 2.98/1.66  %Foreground sorts:
% 2.98/1.66  
% 2.98/1.66  
% 2.98/1.66  %Background operators:
% 2.98/1.66  
% 2.98/1.66  
% 2.98/1.66  %Foreground operators:
% 2.98/1.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.98/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.98/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.98/1.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.98/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.98/1.66  tff('#skF_5', type, '#skF_5': $i).
% 2.98/1.66  tff('#skF_6', type, '#skF_6': $i).
% 2.98/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.98/1.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.98/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.98/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.98/1.66  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.98/1.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.98/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.98/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.98/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.66  
% 2.98/1.67  tff(f_101, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 2.98/1.67  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.98/1.67  tff(f_62, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.98/1.67  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.98/1.67  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.98/1.67  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.98/1.67  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.98/1.67  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.98/1.67  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.98/1.67  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.98/1.67  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.98/1.67  tff(c_40, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.98/1.67  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.98/1.67  tff(c_78, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.98/1.67  tff(c_92, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_78])).
% 2.98/1.67  tff(c_26, plain, (![A_15]: (k2_relat_1(A_15)=k1_xboole_0 | k1_relat_1(A_15)!=k1_xboole_0 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.98/1.67  tff(c_99, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_92, c_26])).
% 2.98/1.67  tff(c_102, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_99])).
% 2.98/1.67  tff(c_122, plain, (![C_64, A_65, B_66]: (v4_relat_1(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.98/1.67  tff(c_136, plain, (v4_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_122])).
% 2.98/1.67  tff(c_22, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(B_14), A_13) | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.98/1.67  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.98/1.67  tff(c_54, plain, (![C_44, A_45]: (r2_hidden(C_44, k1_zfmisc_1(A_45)) | ~r1_tarski(C_44, A_45))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.98/1.67  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.98/1.67  tff(c_58, plain, (![C_44, A_45]: (m1_subset_1(C_44, k1_zfmisc_1(A_45)) | ~r1_tarski(C_44, A_45))), inference(resolution, [status(thm)], [c_54, c_16])).
% 2.98/1.67  tff(c_163, plain, (![A_73, C_74, B_75]: (m1_subset_1(A_73, C_74) | ~m1_subset_1(B_75, k1_zfmisc_1(C_74)) | ~r2_hidden(A_73, B_75))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.98/1.67  tff(c_186, plain, (![A_80, A_81, C_82]: (m1_subset_1(A_80, A_81) | ~r2_hidden(A_80, C_82) | ~r1_tarski(C_82, A_81))), inference(resolution, [status(thm)], [c_58, c_163])).
% 2.98/1.67  tff(c_192, plain, (![A_1, A_81]: (m1_subset_1('#skF_1'(A_1), A_81) | ~r1_tarski(A_1, A_81) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_2, c_186])).
% 2.98/1.67  tff(c_218, plain, (![A_88, B_89, C_90]: (k1_relset_1(A_88, B_89, C_90)=k1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.98/1.67  tff(c_237, plain, (k1_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_218])).
% 2.98/1.67  tff(c_69, plain, (![D_48]: (~r2_hidden(D_48, k1_relset_1('#skF_5', '#skF_4', '#skF_6')) | ~m1_subset_1(D_48, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.98/1.67  tff(c_74, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_5', '#skF_4', '#skF_6')), '#skF_5') | k1_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_69])).
% 2.98/1.67  tff(c_104, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_5', '#skF_4', '#skF_6')), '#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 2.98/1.67  tff(c_238, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_237, c_104])).
% 2.98/1.67  tff(c_246, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5') | k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_192, c_238])).
% 2.98/1.67  tff(c_249, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_102, c_246])).
% 2.98/1.67  tff(c_252, plain, (~v4_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_22, c_249])).
% 2.98/1.67  tff(c_256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_136, c_252])).
% 2.98/1.67  tff(c_257, plain, (k1_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_74])).
% 2.98/1.67  tff(c_407, plain, (![A_128, B_129, C_130]: (k1_relset_1(A_128, B_129, C_130)=k1_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.98/1.67  tff(c_422, plain, (k1_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_407])).
% 2.98/1.67  tff(c_427, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_257, c_422])).
% 2.98/1.67  tff(c_429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_427])).
% 2.98/1.67  tff(c_430, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_99])).
% 2.98/1.67  tff(c_611, plain, (![A_164, B_165, C_166]: (k2_relset_1(A_164, B_165, C_166)=k2_relat_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.98/1.67  tff(c_626, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_611])).
% 2.98/1.67  tff(c_631, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_430, c_626])).
% 2.98/1.67  tff(c_633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_631])).
% 2.98/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.67  
% 2.98/1.67  Inference rules
% 2.98/1.67  ----------------------
% 2.98/1.67  #Ref     : 0
% 2.98/1.67  #Sup     : 118
% 2.98/1.67  #Fact    : 0
% 2.98/1.67  #Define  : 0
% 2.98/1.67  #Split   : 3
% 2.98/1.67  #Chain   : 0
% 2.98/1.67  #Close   : 0
% 2.98/1.67  
% 2.98/1.67  Ordering : KBO
% 2.98/1.67  
% 2.98/1.67  Simplification rules
% 2.98/1.67  ----------------------
% 2.98/1.67  #Subsume      : 2
% 2.98/1.67  #Demod        : 17
% 2.98/1.67  #Tautology    : 20
% 2.98/1.67  #SimpNegUnit  : 4
% 2.98/1.67  #BackRed      : 6
% 2.98/1.67  
% 2.98/1.67  #Partial instantiations: 0
% 2.98/1.67  #Strategies tried      : 1
% 2.98/1.67  
% 2.98/1.67  Timing (in seconds)
% 2.98/1.67  ----------------------
% 2.98/1.68  Preprocessing        : 0.43
% 2.98/1.68  Parsing              : 0.19
% 2.98/1.68  CNF conversion       : 0.04
% 2.98/1.68  Main loop            : 0.46
% 2.98/1.68  Inferencing          : 0.18
% 2.98/1.68  Reduction            : 0.12
% 2.98/1.68  Demodulation         : 0.07
% 2.98/1.68  BG Simplification    : 0.03
% 2.98/1.68  Subsumption          : 0.07
% 2.98/1.68  Abstraction          : 0.03
% 2.98/1.68  MUC search           : 0.00
% 2.98/1.68  Cooper               : 0.00
% 2.98/1.68  Total                : 0.92
% 2.98/1.68  Index Insertion      : 0.00
% 2.98/1.68  Index Deletion       : 0.00
% 2.98/1.68  Index Matching       : 0.00
% 2.98/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
