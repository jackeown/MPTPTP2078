%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:12 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   71 (  94 expanded)
%              Number of leaves         :   38 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :   99 ( 178 expanded)
%              Number of equality atoms :   34 (  59 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_102,axiom,(
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

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_68,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_149,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_153,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_149])).

tff(c_74,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_72,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_245,plain,(
    ! [A_115,B_116,C_117] :
      ( k1_relset_1(A_115,B_116,C_117) = k1_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_249,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_245])).

tff(c_423,plain,(
    ! [B_151,A_152,C_153] :
      ( k1_xboole_0 = B_151
      | k1_relset_1(A_152,B_151,C_153) = A_152
      | ~ v1_funct_2(C_153,A_152,B_151)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_152,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_426,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_70,c_423])).

tff(c_429,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_249,c_426])).

tff(c_430,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_429])).

tff(c_366,plain,(
    ! [A_138,C_139] :
      ( r2_hidden(k4_tarski(A_138,k1_funct_1(C_139,A_138)),C_139)
      | ~ r2_hidden(A_138,k1_relat_1(C_139))
      | ~ v1_funct_1(C_139)
      | ~ v1_relat_1(C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_40,plain,(
    ! [C_22,A_19,B_20] :
      ( r2_hidden(C_22,A_19)
      | ~ r2_hidden(C_22,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_498,plain,(
    ! [A_178,C_179,A_180] :
      ( r2_hidden(k4_tarski(A_178,k1_funct_1(C_179,A_178)),A_180)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(A_180))
      | ~ r2_hidden(A_178,k1_relat_1(C_179))
      | ~ v1_funct_1(C_179)
      | ~ v1_relat_1(C_179) ) ),
    inference(resolution,[status(thm)],[c_366,c_40])).

tff(c_36,plain,(
    ! [D_18,B_16,A_15,C_17] :
      ( D_18 = B_16
      | ~ r2_hidden(k4_tarski(A_15,B_16),k2_zfmisc_1(C_17,k1_tarski(D_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_550,plain,(
    ! [C_189,A_190,D_191,C_192] :
      ( k1_funct_1(C_189,A_190) = D_191
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(C_192,k1_tarski(D_191))))
      | ~ r2_hidden(A_190,k1_relat_1(C_189))
      | ~ v1_funct_1(C_189)
      | ~ v1_relat_1(C_189) ) ),
    inference(resolution,[status(thm)],[c_498,c_36])).

tff(c_552,plain,(
    ! [A_190] :
      ( k1_funct_1('#skF_6',A_190) = '#skF_4'
      | ~ r2_hidden(A_190,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_70,c_550])).

tff(c_556,plain,(
    ! [A_193] :
      ( k1_funct_1('#skF_6',A_193) = '#skF_4'
      | ~ r2_hidden(A_193,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_74,c_430,c_552])).

tff(c_571,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_68,c_556])).

tff(c_578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_571])).

tff(c_579,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_429])).

tff(c_28,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_108,plain,(
    ! [A_59,B_60] : k1_enumset1(A_59,A_59,B_60) = k2_tarski(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [E_8,A_2,B_3] : r2_hidden(E_8,k1_enumset1(A_2,B_3,E_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_135,plain,(
    ! [B_61,A_62] : r2_hidden(B_61,k2_tarski(A_62,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_6])).

tff(c_143,plain,(
    ! [A_63] : r2_hidden(A_63,k1_tarski(A_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_135])).

tff(c_48,plain,(
    ! [B_27,A_26] :
      ( ~ r1_tarski(B_27,A_26)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_147,plain,(
    ! [A_63] : ~ r1_tarski(k1_tarski(A_63),A_63) ),
    inference(resolution,[status(thm)],[c_143,c_48])).

tff(c_607,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_579,c_147])).

tff(c_615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_607])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:45:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.40  
% 2.81/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.41  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.81/1.41  
% 2.81/1.41  %Foreground sorts:
% 2.81/1.41  
% 2.81/1.41  
% 2.81/1.41  %Background operators:
% 2.81/1.41  
% 2.81/1.41  
% 2.81/1.41  %Foreground operators:
% 2.81/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.81/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.81/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.81/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.81/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.81/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.81/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.81/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.81/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.81/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.81/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.81/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.81/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.81/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.41  
% 2.81/1.42  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.81/1.42  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.81/1.42  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.81/1.42  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.81/1.42  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.81/1.42  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.81/1.42  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.81/1.42  tff(f_54, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.81/1.42  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.81/1.42  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.81/1.42  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.81/1.42  tff(f_76, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.81/1.42  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.81/1.42  tff(c_66, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.81/1.42  tff(c_68, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.81/1.42  tff(c_70, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.81/1.42  tff(c_149, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.81/1.42  tff(c_153, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_149])).
% 2.81/1.42  tff(c_74, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.81/1.42  tff(c_72, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.81/1.42  tff(c_245, plain, (![A_115, B_116, C_117]: (k1_relset_1(A_115, B_116, C_117)=k1_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.81/1.42  tff(c_249, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_245])).
% 2.81/1.42  tff(c_423, plain, (![B_151, A_152, C_153]: (k1_xboole_0=B_151 | k1_relset_1(A_152, B_151, C_153)=A_152 | ~v1_funct_2(C_153, A_152, B_151) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_152, B_151))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.81/1.42  tff(c_426, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_423])).
% 2.81/1.42  tff(c_429, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_249, c_426])).
% 2.81/1.42  tff(c_430, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_429])).
% 2.81/1.42  tff(c_366, plain, (![A_138, C_139]: (r2_hidden(k4_tarski(A_138, k1_funct_1(C_139, A_138)), C_139) | ~r2_hidden(A_138, k1_relat_1(C_139)) | ~v1_funct_1(C_139) | ~v1_relat_1(C_139))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.81/1.42  tff(c_40, plain, (![C_22, A_19, B_20]: (r2_hidden(C_22, A_19) | ~r2_hidden(C_22, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.81/1.42  tff(c_498, plain, (![A_178, C_179, A_180]: (r2_hidden(k4_tarski(A_178, k1_funct_1(C_179, A_178)), A_180) | ~m1_subset_1(C_179, k1_zfmisc_1(A_180)) | ~r2_hidden(A_178, k1_relat_1(C_179)) | ~v1_funct_1(C_179) | ~v1_relat_1(C_179))), inference(resolution, [status(thm)], [c_366, c_40])).
% 2.81/1.42  tff(c_36, plain, (![D_18, B_16, A_15, C_17]: (D_18=B_16 | ~r2_hidden(k4_tarski(A_15, B_16), k2_zfmisc_1(C_17, k1_tarski(D_18))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.81/1.42  tff(c_550, plain, (![C_189, A_190, D_191, C_192]: (k1_funct_1(C_189, A_190)=D_191 | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(C_192, k1_tarski(D_191)))) | ~r2_hidden(A_190, k1_relat_1(C_189)) | ~v1_funct_1(C_189) | ~v1_relat_1(C_189))), inference(resolution, [status(thm)], [c_498, c_36])).
% 2.81/1.42  tff(c_552, plain, (![A_190]: (k1_funct_1('#skF_6', A_190)='#skF_4' | ~r2_hidden(A_190, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_70, c_550])).
% 2.81/1.42  tff(c_556, plain, (![A_193]: (k1_funct_1('#skF_6', A_193)='#skF_4' | ~r2_hidden(A_193, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_74, c_430, c_552])).
% 2.81/1.42  tff(c_571, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_68, c_556])).
% 2.81/1.42  tff(c_578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_571])).
% 2.81/1.42  tff(c_579, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_429])).
% 2.81/1.42  tff(c_28, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.81/1.42  tff(c_108, plain, (![A_59, B_60]: (k1_enumset1(A_59, A_59, B_60)=k2_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.42  tff(c_6, plain, (![E_8, A_2, B_3]: (r2_hidden(E_8, k1_enumset1(A_2, B_3, E_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.81/1.42  tff(c_135, plain, (![B_61, A_62]: (r2_hidden(B_61, k2_tarski(A_62, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_6])).
% 2.81/1.42  tff(c_143, plain, (![A_63]: (r2_hidden(A_63, k1_tarski(A_63)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_135])).
% 2.81/1.42  tff(c_48, plain, (![B_27, A_26]: (~r1_tarski(B_27, A_26) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.81/1.42  tff(c_147, plain, (![A_63]: (~r1_tarski(k1_tarski(A_63), A_63))), inference(resolution, [status(thm)], [c_143, c_48])).
% 2.81/1.42  tff(c_607, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_579, c_147])).
% 2.81/1.42  tff(c_615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_607])).
% 2.81/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.42  
% 2.81/1.42  Inference rules
% 2.81/1.42  ----------------------
% 2.81/1.42  #Ref     : 0
% 2.81/1.42  #Sup     : 120
% 2.81/1.42  #Fact    : 0
% 2.81/1.42  #Define  : 0
% 2.81/1.42  #Split   : 2
% 2.81/1.42  #Chain   : 0
% 2.81/1.42  #Close   : 0
% 2.81/1.42  
% 2.81/1.42  Ordering : KBO
% 2.81/1.42  
% 2.81/1.42  Simplification rules
% 2.81/1.42  ----------------------
% 2.81/1.42  #Subsume      : 10
% 2.81/1.42  #Demod        : 17
% 2.81/1.42  #Tautology    : 27
% 2.81/1.42  #SimpNegUnit  : 1
% 2.81/1.42  #BackRed      : 4
% 2.81/1.42  
% 2.81/1.42  #Partial instantiations: 0
% 2.81/1.42  #Strategies tried      : 1
% 2.81/1.42  
% 2.81/1.42  Timing (in seconds)
% 2.81/1.42  ----------------------
% 2.81/1.42  Preprocessing        : 0.33
% 2.81/1.42  Parsing              : 0.17
% 2.81/1.42  CNF conversion       : 0.02
% 2.81/1.42  Main loop            : 0.33
% 2.81/1.42  Inferencing          : 0.12
% 2.81/1.42  Reduction            : 0.09
% 2.81/1.42  Demodulation         : 0.07
% 2.81/1.42  BG Simplification    : 0.02
% 2.81/1.42  Subsumption          : 0.07
% 2.81/1.42  Abstraction          : 0.02
% 2.81/1.42  MUC search           : 0.00
% 2.81/1.42  Cooper               : 0.00
% 2.81/1.42  Total                : 0.69
% 2.81/1.42  Index Insertion      : 0.00
% 2.81/1.42  Index Deletion       : 0.00
% 2.81/1.42  Index Matching       : 0.00
% 2.81/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
