%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:15 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   60 (  83 expanded)
%              Number of leaves         :   33 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   87 ( 166 expanded)
%              Number of equality atoms :   28 (  53 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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

tff(f_66,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_44,plain,(
    k1_funct_1('#skF_4','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_72,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_76,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_72])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_1',k1_tarski('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_110,plain,(
    ! [A_57,B_58,C_59] :
      ( k1_relset_1(A_57,B_58,C_59) = k1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_114,plain,(
    k1_relset_1('#skF_1',k1_tarski('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_110])).

tff(c_137,plain,(
    ! [B_69,A_70,C_71] :
      ( k1_xboole_0 = B_69
      | k1_relset_1(A_70,B_69,C_71) = A_70
      | ~ v1_funct_2(C_71,A_70,B_69)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_140,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_relset_1('#skF_1',k1_tarski('#skF_2'),'#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_137])).

tff(c_143,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_114,c_140])).

tff(c_144,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_122,plain,(
    ! [B_65,A_66] :
      ( r2_hidden(k4_tarski(B_65,k1_funct_1(A_66,B_65)),A_66)
      | ~ r2_hidden(B_65,k1_relat_1(A_66))
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [C_15,A_12,B_13] :
      ( r2_hidden(C_15,A_12)
      | ~ r2_hidden(C_15,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_197,plain,(
    ! [B_88,A_89,A_90] :
      ( r2_hidden(k4_tarski(B_88,k1_funct_1(A_89,B_88)),A_90)
      | ~ m1_subset_1(A_89,k1_zfmisc_1(A_90))
      | ~ r2_hidden(B_88,k1_relat_1(A_89))
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(resolution,[status(thm)],[c_122,c_18])).

tff(c_14,plain,(
    ! [D_11,B_9,A_8,C_10] :
      ( D_11 = B_9
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,k1_tarski(D_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_222,plain,(
    ! [A_95,B_96,D_97,C_98] :
      ( k1_funct_1(A_95,B_96) = D_97
      | ~ m1_subset_1(A_95,k1_zfmisc_1(k2_zfmisc_1(C_98,k1_tarski(D_97))))
      | ~ r2_hidden(B_96,k1_relat_1(A_95))
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_197,c_14])).

tff(c_224,plain,(
    ! [B_96] :
      ( k1_funct_1('#skF_4',B_96) = '#skF_2'
      | ~ r2_hidden(B_96,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_222])).

tff(c_228,plain,(
    ! [B_99] :
      ( k1_funct_1('#skF_4',B_99) = '#skF_2'
      | ~ r2_hidden(B_99,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_52,c_144,c_224])).

tff(c_242,plain,(
    k1_funct_1('#skF_4','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_46,c_228])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_242])).

tff(c_250,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_10,plain,(
    ! [A_7] : ~ v1_xboole_0(k1_tarski(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_265,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_10])).

tff(c_270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:00:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.40  
% 2.37/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.41  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.37/1.41  
% 2.37/1.41  %Foreground sorts:
% 2.37/1.41  
% 2.37/1.41  
% 2.37/1.41  %Background operators:
% 2.37/1.41  
% 2.37/1.41  
% 2.37/1.41  %Foreground operators:
% 2.37/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.37/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.37/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.37/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.37/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.37/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.37/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.37/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.37/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.37/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.37/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.37/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.41  
% 2.37/1.42  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.37/1.42  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.37/1.42  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.37/1.42  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.37/1.42  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.37/1.42  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 2.37/1.42  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.37/1.42  tff(f_41, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.37/1.42  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.37/1.42  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.37/1.42  tff(c_44, plain, (k1_funct_1('#skF_4', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.37/1.42  tff(c_46, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.37/1.42  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.37/1.42  tff(c_72, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.37/1.42  tff(c_76, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_72])).
% 2.37/1.42  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.37/1.42  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_1', k1_tarski('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.37/1.42  tff(c_110, plain, (![A_57, B_58, C_59]: (k1_relset_1(A_57, B_58, C_59)=k1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.37/1.42  tff(c_114, plain, (k1_relset_1('#skF_1', k1_tarski('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_110])).
% 2.37/1.42  tff(c_137, plain, (![B_69, A_70, C_71]: (k1_xboole_0=B_69 | k1_relset_1(A_70, B_69, C_71)=A_70 | ~v1_funct_2(C_71, A_70, B_69) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.37/1.42  tff(c_140, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_relset_1('#skF_1', k1_tarski('#skF_2'), '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_137])).
% 2.37/1.42  tff(c_143, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_114, c_140])).
% 2.37/1.42  tff(c_144, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(splitLeft, [status(thm)], [c_143])).
% 2.37/1.42  tff(c_122, plain, (![B_65, A_66]: (r2_hidden(k4_tarski(B_65, k1_funct_1(A_66, B_65)), A_66) | ~r2_hidden(B_65, k1_relat_1(A_66)) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.37/1.42  tff(c_18, plain, (![C_15, A_12, B_13]: (r2_hidden(C_15, A_12) | ~r2_hidden(C_15, B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.37/1.42  tff(c_197, plain, (![B_88, A_89, A_90]: (r2_hidden(k4_tarski(B_88, k1_funct_1(A_89, B_88)), A_90) | ~m1_subset_1(A_89, k1_zfmisc_1(A_90)) | ~r2_hidden(B_88, k1_relat_1(A_89)) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(resolution, [status(thm)], [c_122, c_18])).
% 2.37/1.42  tff(c_14, plain, (![D_11, B_9, A_8, C_10]: (D_11=B_9 | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(C_10, k1_tarski(D_11))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.37/1.42  tff(c_222, plain, (![A_95, B_96, D_97, C_98]: (k1_funct_1(A_95, B_96)=D_97 | ~m1_subset_1(A_95, k1_zfmisc_1(k2_zfmisc_1(C_98, k1_tarski(D_97)))) | ~r2_hidden(B_96, k1_relat_1(A_95)) | ~v1_funct_1(A_95) | ~v1_relat_1(A_95))), inference(resolution, [status(thm)], [c_197, c_14])).
% 2.37/1.42  tff(c_224, plain, (![B_96]: (k1_funct_1('#skF_4', B_96)='#skF_2' | ~r2_hidden(B_96, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_222])).
% 2.37/1.42  tff(c_228, plain, (![B_99]: (k1_funct_1('#skF_4', B_99)='#skF_2' | ~r2_hidden(B_99, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_52, c_144, c_224])).
% 2.37/1.42  tff(c_242, plain, (k1_funct_1('#skF_4', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_46, c_228])).
% 2.37/1.42  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_242])).
% 2.37/1.42  tff(c_250, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_143])).
% 2.37/1.42  tff(c_10, plain, (![A_7]: (~v1_xboole_0(k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.37/1.42  tff(c_265, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_250, c_10])).
% 2.37/1.42  tff(c_270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_265])).
% 2.37/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.42  
% 2.37/1.42  Inference rules
% 2.37/1.42  ----------------------
% 2.37/1.42  #Ref     : 0
% 2.37/1.42  #Sup     : 47
% 2.37/1.42  #Fact    : 0
% 2.37/1.42  #Define  : 0
% 2.37/1.42  #Split   : 2
% 2.37/1.42  #Chain   : 0
% 2.37/1.42  #Close   : 0
% 2.37/1.42  
% 2.37/1.42  Ordering : KBO
% 2.37/1.42  
% 2.37/1.42  Simplification rules
% 2.37/1.42  ----------------------
% 2.37/1.42  #Subsume      : 3
% 2.37/1.42  #Demod        : 19
% 2.37/1.42  #Tautology    : 18
% 2.37/1.42  #SimpNegUnit  : 1
% 2.37/1.42  #BackRed      : 4
% 2.37/1.42  
% 2.37/1.42  #Partial instantiations: 0
% 2.37/1.42  #Strategies tried      : 1
% 2.37/1.42  
% 2.37/1.42  Timing (in seconds)
% 2.37/1.42  ----------------------
% 2.37/1.42  Preprocessing        : 0.37
% 2.37/1.42  Parsing              : 0.19
% 2.37/1.42  CNF conversion       : 0.02
% 2.37/1.42  Main loop            : 0.21
% 2.37/1.42  Inferencing          : 0.08
% 2.37/1.42  Reduction            : 0.06
% 2.37/1.42  Demodulation         : 0.04
% 2.37/1.42  BG Simplification    : 0.02
% 2.37/1.42  Subsumption          : 0.04
% 2.37/1.42  Abstraction          : 0.01
% 2.37/1.42  MUC search           : 0.00
% 2.37/1.42  Cooper               : 0.00
% 2.37/1.42  Total                : 0.61
% 2.37/1.42  Index Insertion      : 0.00
% 2.37/1.42  Index Deletion       : 0.00
% 2.37/1.42  Index Matching       : 0.00
% 2.62/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
