%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:13 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   74 (  97 expanded)
%              Number of leaves         :   39 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :  106 ( 185 expanded)
%              Number of equality atoms :   39 (  64 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_113,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_74,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_76,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_78,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_128,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_132,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_128])).

tff(c_82,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_80,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_331,plain,(
    ! [A_171,B_172,C_173] :
      ( k1_relset_1(A_171,B_172,C_173) = k1_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_335,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_331])).

tff(c_460,plain,(
    ! [B_202,A_203,C_204] :
      ( k1_xboole_0 = B_202
      | k1_relset_1(A_203,B_202,C_204) = A_203
      | ~ v1_funct_2(C_204,A_203,B_202)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_203,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_463,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_78,c_460])).

tff(c_466,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_335,c_463])).

tff(c_467,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_466])).

tff(c_350,plain,(
    ! [B_180,A_181] :
      ( r2_hidden(k4_tarski(B_180,k1_funct_1(A_181,B_180)),A_181)
      | ~ r2_hidden(B_180,k1_relat_1(A_181))
      | ~ v1_funct_1(A_181)
      | ~ v1_relat_1(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_46,plain,(
    ! [C_23,A_20,B_21] :
      ( r2_hidden(C_23,A_20)
      | ~ r2_hidden(C_23,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_622,plain,(
    ! [B_226,A_227,A_228] :
      ( r2_hidden(k4_tarski(B_226,k1_funct_1(A_227,B_226)),A_228)
      | ~ m1_subset_1(A_227,k1_zfmisc_1(A_228))
      | ~ r2_hidden(B_226,k1_relat_1(A_227))
      | ~ v1_funct_1(A_227)
      | ~ v1_relat_1(A_227) ) ),
    inference(resolution,[status(thm)],[c_350,c_46])).

tff(c_12,plain,(
    ! [D_11,B_9,A_8,C_10] :
      ( D_11 = B_9
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,k1_tarski(D_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_719,plain,(
    ! [A_245,B_246,D_247,C_248] :
      ( k1_funct_1(A_245,B_246) = D_247
      | ~ m1_subset_1(A_245,k1_zfmisc_1(k2_zfmisc_1(C_248,k1_tarski(D_247))))
      | ~ r2_hidden(B_246,k1_relat_1(A_245))
      | ~ v1_funct_1(A_245)
      | ~ v1_relat_1(A_245) ) ),
    inference(resolution,[status(thm)],[c_622,c_12])).

tff(c_721,plain,(
    ! [B_246] :
      ( k1_funct_1('#skF_6',B_246) = '#skF_4'
      | ~ r2_hidden(B_246,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_78,c_719])).

tff(c_725,plain,(
    ! [B_249] :
      ( k1_funct_1('#skF_6',B_249) = '#skF_4'
      | ~ r2_hidden(B_249,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_82,c_467,c_721])).

tff(c_739,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_76,c_725])).

tff(c_746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_739])).

tff(c_747,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_466])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_77,B_78,C_79] : k2_enumset1(A_77,A_77,B_78,C_79) = k1_enumset1(A_77,B_78,C_79) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [F_19,A_12,C_14,D_15] : r2_hidden(F_19,k2_enumset1(A_12,F_19,C_14,D_15)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_165,plain,(
    ! [A_80,B_81,C_82] : r2_hidden(A_80,k1_enumset1(A_80,B_81,C_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_22])).

tff(c_173,plain,(
    ! [A_83,B_84] : r2_hidden(A_83,k2_tarski(A_83,B_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_165])).

tff(c_181,plain,(
    ! [A_85] : r2_hidden(A_85,k1_tarski(A_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_173])).

tff(c_56,plain,(
    ! [B_30,A_29] :
      ( ~ r1_tarski(B_30,A_29)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_185,plain,(
    ! [A_85] : ~ r1_tarski(k1_tarski(A_85),A_85) ),
    inference(resolution,[status(thm)],[c_181,c_56])).

tff(c_772,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_747,c_185])).

tff(c_780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_772])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:29:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.55  
% 3.27/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.55  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 3.27/1.55  
% 3.27/1.55  %Foreground sorts:
% 3.27/1.55  
% 3.27/1.55  
% 3.27/1.55  %Background operators:
% 3.27/1.55  
% 3.27/1.55  
% 3.27/1.55  %Foreground operators:
% 3.27/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.27/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.27/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.27/1.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.27/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.27/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.27/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.27/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.27/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.27/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.27/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.27/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.55  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.27/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.55  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.27/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.27/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.27/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.27/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.55  
% 3.27/1.57  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.27/1.57  tff(f_124, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.27/1.57  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.27/1.57  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.27/1.57  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.27/1.57  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 3.27/1.57  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.27/1.57  tff(f_39, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 3.27/1.57  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.27/1.57  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.27/1.57  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.27/1.57  tff(f_57, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 3.27/1.57  tff(f_87, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.27/1.57  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.27/1.57  tff(c_74, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.27/1.57  tff(c_76, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.27/1.57  tff(c_78, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.27/1.57  tff(c_128, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.27/1.57  tff(c_132, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_78, c_128])).
% 3.27/1.57  tff(c_82, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.27/1.57  tff(c_80, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.27/1.57  tff(c_331, plain, (![A_171, B_172, C_173]: (k1_relset_1(A_171, B_172, C_173)=k1_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.27/1.57  tff(c_335, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_78, c_331])).
% 3.27/1.57  tff(c_460, plain, (![B_202, A_203, C_204]: (k1_xboole_0=B_202 | k1_relset_1(A_203, B_202, C_204)=A_203 | ~v1_funct_2(C_204, A_203, B_202) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_203, B_202))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.27/1.57  tff(c_463, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_78, c_460])).
% 3.27/1.57  tff(c_466, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_335, c_463])).
% 3.27/1.57  tff(c_467, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_466])).
% 3.27/1.57  tff(c_350, plain, (![B_180, A_181]: (r2_hidden(k4_tarski(B_180, k1_funct_1(A_181, B_180)), A_181) | ~r2_hidden(B_180, k1_relat_1(A_181)) | ~v1_funct_1(A_181) | ~v1_relat_1(A_181))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.27/1.57  tff(c_46, plain, (![C_23, A_20, B_21]: (r2_hidden(C_23, A_20) | ~r2_hidden(C_23, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.27/1.57  tff(c_622, plain, (![B_226, A_227, A_228]: (r2_hidden(k4_tarski(B_226, k1_funct_1(A_227, B_226)), A_228) | ~m1_subset_1(A_227, k1_zfmisc_1(A_228)) | ~r2_hidden(B_226, k1_relat_1(A_227)) | ~v1_funct_1(A_227) | ~v1_relat_1(A_227))), inference(resolution, [status(thm)], [c_350, c_46])).
% 3.27/1.57  tff(c_12, plain, (![D_11, B_9, A_8, C_10]: (D_11=B_9 | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(C_10, k1_tarski(D_11))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.27/1.57  tff(c_719, plain, (![A_245, B_246, D_247, C_248]: (k1_funct_1(A_245, B_246)=D_247 | ~m1_subset_1(A_245, k1_zfmisc_1(k2_zfmisc_1(C_248, k1_tarski(D_247)))) | ~r2_hidden(B_246, k1_relat_1(A_245)) | ~v1_funct_1(A_245) | ~v1_relat_1(A_245))), inference(resolution, [status(thm)], [c_622, c_12])).
% 3.27/1.57  tff(c_721, plain, (![B_246]: (k1_funct_1('#skF_6', B_246)='#skF_4' | ~r2_hidden(B_246, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_78, c_719])).
% 3.27/1.57  tff(c_725, plain, (![B_249]: (k1_funct_1('#skF_6', B_249)='#skF_4' | ~r2_hidden(B_249, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_82, c_467, c_721])).
% 3.27/1.57  tff(c_739, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_76, c_725])).
% 3.27/1.57  tff(c_746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_739])).
% 3.27/1.57  tff(c_747, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_466])).
% 3.27/1.57  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.27/1.57  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.57  tff(c_135, plain, (![A_77, B_78, C_79]: (k2_enumset1(A_77, A_77, B_78, C_79)=k1_enumset1(A_77, B_78, C_79))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.27/1.57  tff(c_22, plain, (![F_19, A_12, C_14, D_15]: (r2_hidden(F_19, k2_enumset1(A_12, F_19, C_14, D_15)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.27/1.57  tff(c_165, plain, (![A_80, B_81, C_82]: (r2_hidden(A_80, k1_enumset1(A_80, B_81, C_82)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_22])).
% 3.27/1.57  tff(c_173, plain, (![A_83, B_84]: (r2_hidden(A_83, k2_tarski(A_83, B_84)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_165])).
% 3.27/1.57  tff(c_181, plain, (![A_85]: (r2_hidden(A_85, k1_tarski(A_85)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_173])).
% 3.27/1.57  tff(c_56, plain, (![B_30, A_29]: (~r1_tarski(B_30, A_29) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.27/1.57  tff(c_185, plain, (![A_85]: (~r1_tarski(k1_tarski(A_85), A_85))), inference(resolution, [status(thm)], [c_181, c_56])).
% 3.27/1.57  tff(c_772, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_747, c_185])).
% 3.27/1.57  tff(c_780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_772])).
% 3.27/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.57  
% 3.27/1.57  Inference rules
% 3.27/1.57  ----------------------
% 3.27/1.57  #Ref     : 0
% 3.27/1.57  #Sup     : 158
% 3.27/1.57  #Fact    : 0
% 3.27/1.57  #Define  : 0
% 3.27/1.57  #Split   : 4
% 3.27/1.57  #Chain   : 0
% 3.27/1.57  #Close   : 0
% 3.27/1.57  
% 3.27/1.57  Ordering : KBO
% 3.27/1.57  
% 3.27/1.57  Simplification rules
% 3.27/1.57  ----------------------
% 3.27/1.57  #Subsume      : 24
% 3.27/1.57  #Demod        : 27
% 3.27/1.57  #Tautology    : 34
% 3.27/1.57  #SimpNegUnit  : 1
% 3.27/1.57  #BackRed      : 4
% 3.27/1.57  
% 3.27/1.57  #Partial instantiations: 0
% 3.27/1.57  #Strategies tried      : 1
% 3.27/1.57  
% 3.27/1.57  Timing (in seconds)
% 3.27/1.57  ----------------------
% 3.27/1.57  Preprocessing        : 0.37
% 3.27/1.57  Parsing              : 0.19
% 3.27/1.57  CNF conversion       : 0.03
% 3.27/1.57  Main loop            : 0.37
% 3.27/1.57  Inferencing          : 0.13
% 3.27/1.57  Reduction            : 0.11
% 3.27/1.57  Demodulation         : 0.08
% 3.27/1.57  BG Simplification    : 0.02
% 3.27/1.57  Subsumption          : 0.08
% 3.27/1.57  Abstraction          : 0.03
% 3.27/1.57  MUC search           : 0.00
% 3.27/1.57  Cooper               : 0.00
% 3.27/1.57  Total                : 0.78
% 3.27/1.57  Index Insertion      : 0.00
% 3.27/1.57  Index Deletion       : 0.00
% 3.27/1.57  Index Matching       : 0.00
% 3.27/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
