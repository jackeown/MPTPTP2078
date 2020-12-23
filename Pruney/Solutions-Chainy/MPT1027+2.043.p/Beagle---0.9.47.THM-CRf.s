%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:48 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   71 (4341 expanded)
%              Number of leaves         :   19 (1577 expanded)
%              Depth                    :   13
%              Number of atoms          :  107 (14283 expanded)
%              Number of equality atoms :   48 (4649 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_57,axiom,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26])).

tff(c_28,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_254,plain,(
    ! [B_41,C_42,A_43] :
      ( k1_xboole_0 = B_41
      | v1_funct_2(C_42,A_43,B_41)
      | k1_relset_1(A_43,B_41,C_42) != A_43
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_261,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_254])).

tff(c_271,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_261])).

tff(c_272,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_271])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_283,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_272,c_6])).

tff(c_66,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_70,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_66])).

tff(c_294,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_70])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_325,plain,(
    ! [A_48] :
      ( A_48 = '#skF_2'
      | ~ r1_tarski(A_48,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_272,c_2])).

tff(c_332,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_294,c_325])).

tff(c_107,plain,(
    ! [B_26,C_27,A_28] :
      ( k1_xboole_0 = B_26
      | v1_funct_2(C_27,A_28,B_26)
      | k1_relset_1(A_28,B_26,C_27) != A_28
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_114,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_107])).

tff(c_124,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_114])).

tff(c_125,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_124])).

tff(c_136,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_125,c_6])).

tff(c_142,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_70])).

tff(c_189,plain,(
    ! [A_34] :
      ( A_34 = '#skF_2'
      | ~ r1_tarski(A_34,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_125,c_2])).

tff(c_193,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_142,c_189])).

tff(c_199,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_142])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_6] :
      ( v1_funct_2(k1_xboole_0,A_6,k1_xboole_0)
      | k1_xboole_0 = A_6
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_6,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    ! [A_6] :
      ( v1_funct_2(k1_xboole_0,A_6,k1_xboole_0)
      | k1_xboole_0 = A_6
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_87,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_91,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_87])).

tff(c_132,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_125,c_91])).

tff(c_201,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_193,c_132])).

tff(c_218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_201])).

tff(c_219,plain,(
    ! [A_6] :
      ( v1_funct_2(k1_xboole_0,A_6,k1_xboole_0)
      | k1_xboole_0 = A_6 ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_278,plain,(
    ! [A_6] :
      ( v1_funct_2('#skF_2',A_6,'#skF_2')
      | A_6 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_272,c_272,c_219])).

tff(c_408,plain,(
    ! [A_55] :
      ( v1_funct_2('#skF_3',A_55,'#skF_3')
      | A_55 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_332,c_332,c_278])).

tff(c_345,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_34])).

tff(c_412,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_408,c_345])).

tff(c_344,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_28])).

tff(c_415,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_412,c_344])).

tff(c_423,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_332])).

tff(c_220,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [C_8,B_7] :
      ( v1_funct_2(C_8,k1_xboole_0,B_7)
      | k1_relset_1(k1_xboole_0,B_7,C_8) != k1_xboole_0
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_238,plain,(
    ! [C_38,B_39] :
      ( v1_funct_2(C_38,k1_xboole_0,B_39)
      | k1_relset_1(k1_xboole_0,B_39,C_38) != k1_xboole_0
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_244,plain,(
    ! [B_39] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_39)
      | k1_relset_1(k1_xboole_0,B_39,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_220,c_238])).

tff(c_275,plain,(
    ! [B_39] :
      ( v1_funct_2('#skF_2','#skF_2',B_39)
      | k1_relset_1('#skF_2',B_39,'#skF_2') != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_272,c_272,c_272,c_272,c_244])).

tff(c_493,plain,(
    ! [B_62] :
      ( v1_funct_2('#skF_1','#skF_1',B_62)
      | k1_relset_1('#skF_1',B_62,'#skF_1') != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_423,c_423,c_423,c_423,c_275])).

tff(c_419,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_412,c_345])).

tff(c_496,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_493,c_419])).

tff(c_500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_496])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:44:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.35  
% 2.08/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.36  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.08/1.36  
% 2.08/1.36  %Foreground sorts:
% 2.08/1.36  
% 2.08/1.36  
% 2.08/1.36  %Background operators:
% 2.08/1.36  
% 2.08/1.36  
% 2.08/1.36  %Foreground operators:
% 2.08/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.08/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.08/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.08/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.36  
% 2.31/1.37  tff(f_70, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 2.31/1.37  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.31/1.37  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.31/1.37  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.31/1.37  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.31/1.37  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.31/1.37  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.31/1.37  tff(c_26, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.31/1.37  tff(c_34, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26])).
% 2.31/1.37  tff(c_28, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.31/1.37  tff(c_254, plain, (![B_41, C_42, A_43]: (k1_xboole_0=B_41 | v1_funct_2(C_42, A_43, B_41) | k1_relset_1(A_43, B_41, C_42)!=A_43 | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_41))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.31/1.37  tff(c_261, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_30, c_254])).
% 2.31/1.37  tff(c_271, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_261])).
% 2.31/1.37  tff(c_272, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_34, c_271])).
% 2.31/1.37  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.37  tff(c_283, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_272, c_272, c_6])).
% 2.31/1.37  tff(c_66, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.31/1.37  tff(c_70, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_66])).
% 2.31/1.37  tff(c_294, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_70])).
% 2.31/1.37  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.31/1.37  tff(c_325, plain, (![A_48]: (A_48='#skF_2' | ~r1_tarski(A_48, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_272, c_2])).
% 2.31/1.37  tff(c_332, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_294, c_325])).
% 2.31/1.37  tff(c_107, plain, (![B_26, C_27, A_28]: (k1_xboole_0=B_26 | v1_funct_2(C_27, A_28, B_26) | k1_relset_1(A_28, B_26, C_27)!=A_28 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_26))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.31/1.37  tff(c_114, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_30, c_107])).
% 2.31/1.37  tff(c_124, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_114])).
% 2.31/1.37  tff(c_125, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_34, c_124])).
% 2.31/1.37  tff(c_136, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_125, c_6])).
% 2.31/1.37  tff(c_142, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_70])).
% 2.31/1.37  tff(c_189, plain, (![A_34]: (A_34='#skF_2' | ~r1_tarski(A_34, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_125, c_2])).
% 2.31/1.37  tff(c_193, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_142, c_189])).
% 2.31/1.37  tff(c_199, plain, (r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_142])).
% 2.31/1.37  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.31/1.37  tff(c_14, plain, (![A_6]: (v1_funct_2(k1_xboole_0, A_6, k1_xboole_0) | k1_xboole_0=A_6 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_6, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.31/1.37  tff(c_38, plain, (![A_6]: (v1_funct_2(k1_xboole_0, A_6, k1_xboole_0) | k1_xboole_0=A_6 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 2.31/1.37  tff(c_87, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_38])).
% 2.31/1.37  tff(c_91, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_87])).
% 2.31/1.37  tff(c_132, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_125, c_91])).
% 2.31/1.37  tff(c_201, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_193, c_132])).
% 2.31/1.37  tff(c_218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_199, c_201])).
% 2.31/1.37  tff(c_219, plain, (![A_6]: (v1_funct_2(k1_xboole_0, A_6, k1_xboole_0) | k1_xboole_0=A_6)), inference(splitRight, [status(thm)], [c_38])).
% 2.31/1.37  tff(c_278, plain, (![A_6]: (v1_funct_2('#skF_2', A_6, '#skF_2') | A_6='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_272, c_272, c_272, c_219])).
% 2.31/1.37  tff(c_408, plain, (![A_55]: (v1_funct_2('#skF_3', A_55, '#skF_3') | A_55='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_332, c_332, c_332, c_278])).
% 2.31/1.37  tff(c_345, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_332, c_34])).
% 2.31/1.37  tff(c_412, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_408, c_345])).
% 2.31/1.37  tff(c_344, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_332, c_28])).
% 2.31/1.37  tff(c_415, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_412, c_412, c_344])).
% 2.31/1.37  tff(c_423, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_412, c_332])).
% 2.31/1.37  tff(c_220, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_38])).
% 2.31/1.37  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.37  tff(c_18, plain, (![C_8, B_7]: (v1_funct_2(C_8, k1_xboole_0, B_7) | k1_relset_1(k1_xboole_0, B_7, C_8)!=k1_xboole_0 | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_7))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.31/1.37  tff(c_238, plain, (![C_38, B_39]: (v1_funct_2(C_38, k1_xboole_0, B_39) | k1_relset_1(k1_xboole_0, B_39, C_38)!=k1_xboole_0 | ~m1_subset_1(C_38, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 2.31/1.37  tff(c_244, plain, (![B_39]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_39) | k1_relset_1(k1_xboole_0, B_39, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_220, c_238])).
% 2.31/1.37  tff(c_275, plain, (![B_39]: (v1_funct_2('#skF_2', '#skF_2', B_39) | k1_relset_1('#skF_2', B_39, '#skF_2')!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_272, c_272, c_272, c_272, c_272, c_244])).
% 2.31/1.37  tff(c_493, plain, (![B_62]: (v1_funct_2('#skF_1', '#skF_1', B_62) | k1_relset_1('#skF_1', B_62, '#skF_1')!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_423, c_423, c_423, c_423, c_423, c_275])).
% 2.31/1.37  tff(c_419, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_412, c_412, c_345])).
% 2.31/1.37  tff(c_496, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_493, c_419])).
% 2.31/1.37  tff(c_500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_415, c_496])).
% 2.31/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.37  
% 2.31/1.37  Inference rules
% 2.31/1.37  ----------------------
% 2.31/1.37  #Ref     : 0
% 2.31/1.37  #Sup     : 100
% 2.31/1.37  #Fact    : 0
% 2.31/1.37  #Define  : 0
% 2.31/1.37  #Split   : 1
% 2.31/1.37  #Chain   : 0
% 2.31/1.37  #Close   : 0
% 2.31/1.37  
% 2.31/1.37  Ordering : KBO
% 2.31/1.37  
% 2.31/1.37  Simplification rules
% 2.31/1.37  ----------------------
% 2.31/1.37  #Subsume      : 4
% 2.31/1.37  #Demod        : 156
% 2.31/1.37  #Tautology    : 80
% 2.31/1.37  #SimpNegUnit  : 2
% 2.31/1.37  #BackRed      : 60
% 2.31/1.37  
% 2.31/1.37  #Partial instantiations: 0
% 2.31/1.37  #Strategies tried      : 1
% 2.31/1.37  
% 2.31/1.37  Timing (in seconds)
% 2.31/1.37  ----------------------
% 2.31/1.37  Preprocessing        : 0.28
% 2.31/1.37  Parsing              : 0.15
% 2.31/1.37  CNF conversion       : 0.02
% 2.31/1.37  Main loop            : 0.25
% 2.31/1.37  Inferencing          : 0.09
% 2.31/1.37  Reduction            : 0.08
% 2.31/1.38  Demodulation         : 0.05
% 2.31/1.38  BG Simplification    : 0.01
% 2.31/1.38  Subsumption          : 0.04
% 2.31/1.38  Abstraction          : 0.01
% 2.31/1.38  MUC search           : 0.00
% 2.31/1.38  Cooper               : 0.00
% 2.31/1.38  Total                : 0.56
% 2.31/1.38  Index Insertion      : 0.00
% 2.31/1.38  Index Deletion       : 0.00
% 2.31/1.38  Index Matching       : 0.00
% 2.31/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
