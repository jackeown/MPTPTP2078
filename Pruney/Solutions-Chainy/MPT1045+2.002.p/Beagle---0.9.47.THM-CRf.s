%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:05 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 214 expanded)
%              Number of leaves         :   24 (  77 expanded)
%              Depth                    :    9
%              Number of atoms          :  123 ( 540 expanded)
%              Number of equality atoms :   37 ( 266 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k5_partfun1(A,B,k3_partfun1(C,A,B)) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k3_partfun1(C,A,B) = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_partfun1(C,A)
      <=> k5_partfun1(A,B,C) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_27,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,(
    ! [C_22,A_23,B_24] :
      ( k3_partfun1(C_22,A_23,B_24) = C_22
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | ~ v1_funct_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_47,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_2') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_44])).

tff(c_50,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_47])).

tff(c_18,plain,(
    k5_partfun1('#skF_1','#skF_2',k3_partfun1('#skF_3','#skF_1','#skF_2')) != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_51,plain,(
    k5_partfun1('#skF_1','#skF_2','#skF_3') != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_18])).

tff(c_56,plain,(
    ! [A_25,B_26,C_27] :
      ( k5_partfun1(A_25,B_26,C_27) = k1_tarski(C_27)
      | ~ v1_partfun1(C_27,A_25)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_59,plain,
    ( k5_partfun1('#skF_1','#skF_2','#skF_3') = k1_tarski('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_56])).

tff(c_62,plain,
    ( k5_partfun1('#skF_1','#skF_2','#skF_3') = k1_tarski('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_59])).

tff(c_63,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_62])).

tff(c_24,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_71,plain,(
    ! [C_31,A_32,B_33] :
      ( v1_partfun1(C_31,A_32)
      | ~ v1_funct_2(C_31,A_32,B_33)
      | ~ v1_funct_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | v1_xboole_0(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_74,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_71])).

tff(c_77,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_74])).

tff(c_78,plain,(
    v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_77])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_78,c_2])).

tff(c_85,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27,c_81])).

tff(c_86,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_87,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_92,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_87])).

tff(c_93,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_22])).

tff(c_160,plain,(
    ! [C_51,A_52,B_53] :
      ( k3_partfun1(C_51,A_52,B_53) = C_51
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_163,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_160])).

tff(c_166,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_163])).

tff(c_110,plain,(
    k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_3','#skF_1','#skF_1')) != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_92,c_18])).

tff(c_167,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_3') != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_110])).

tff(c_117,plain,(
    ! [C_39,A_40,B_41] :
      ( k3_partfun1(C_39,A_40,B_41) = C_39
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_120,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_117])).

tff(c_123,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_120])).

tff(c_124,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_3') != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_110])).

tff(c_136,plain,(
    ! [A_45,B_46,C_47] :
      ( k5_partfun1(A_45,B_46,C_47) = k1_tarski(C_47)
      | ~ v1_partfun1(C_47,A_45)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_139,plain,
    ( k5_partfun1('#skF_1','#skF_1','#skF_3') = k1_tarski('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_136])).

tff(c_142,plain,
    ( k5_partfun1('#skF_1','#skF_1','#skF_3') = k1_tarski('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_139])).

tff(c_143,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_142])).

tff(c_111,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_partfun1(C_36,A_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38)))
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_115,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_93,c_111])).

tff(c_116,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_94,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_24])).

tff(c_144,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_partfun1(C_48,A_49)
      | ~ v1_funct_2(C_48,A_49,B_50)
      | ~ v1_funct_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | v1_xboole_0(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_147,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_93,c_144])).

tff(c_150,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_94,c_147])).

tff(c_151,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_150])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_151])).

tff(c_153,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_179,plain,(
    ! [A_57,B_58,C_59] :
      ( k5_partfun1(A_57,B_58,C_59) = k1_tarski(C_59)
      | ~ v1_partfun1(C_59,A_57)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_182,plain,
    ( k5_partfun1('#skF_1','#skF_1','#skF_3') = k1_tarski('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_179])).

tff(c_185,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_3') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_153,c_182])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:29:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.28  
% 1.85/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.28  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.85/1.28  
% 1.85/1.28  %Foreground sorts:
% 1.85/1.28  
% 1.85/1.28  
% 1.85/1.28  %Background operators:
% 1.85/1.28  
% 1.85/1.28  
% 1.85/1.28  %Foreground operators:
% 1.85/1.28  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 1.85/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.85/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.85/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.85/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.28  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.85/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.85/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.85/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.28  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 1.85/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.85/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.85/1.28  
% 1.85/1.30  tff(f_79, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k5_partfun1(A, B, k3_partfun1(C, A, B)) = k1_tarski(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t161_funct_2)).
% 1.85/1.30  tff(f_66, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k3_partfun1(C, A, B) = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_partfun1)).
% 1.85/1.30  tff(f_60, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_partfun1(C, A) <=> (k5_partfun1(A, B, C) = k1_tarski(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_partfun1)).
% 1.85/1.30  tff(f_52, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 1.85/1.30  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.85/1.30  tff(f_38, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 1.85/1.30  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.85/1.30  tff(c_20, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.85/1.30  tff(c_27, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_20])).
% 1.85/1.30  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.85/1.30  tff(c_44, plain, (![C_22, A_23, B_24]: (k3_partfun1(C_22, A_23, B_24)=C_22 | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))) | ~v1_funct_1(C_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.85/1.30  tff(c_47, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_2')='#skF_3' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_44])).
% 1.85/1.30  tff(c_50, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_47])).
% 1.85/1.30  tff(c_18, plain, (k5_partfun1('#skF_1', '#skF_2', k3_partfun1('#skF_3', '#skF_1', '#skF_2'))!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.85/1.30  tff(c_51, plain, (k5_partfun1('#skF_1', '#skF_2', '#skF_3')!=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_18])).
% 1.85/1.30  tff(c_56, plain, (![A_25, B_26, C_27]: (k5_partfun1(A_25, B_26, C_27)=k1_tarski(C_27) | ~v1_partfun1(C_27, A_25) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(C_27))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.30  tff(c_59, plain, (k5_partfun1('#skF_1', '#skF_2', '#skF_3')=k1_tarski('#skF_3') | ~v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_56])).
% 1.85/1.30  tff(c_62, plain, (k5_partfun1('#skF_1', '#skF_2', '#skF_3')=k1_tarski('#skF_3') | ~v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_59])).
% 1.85/1.30  tff(c_63, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_51, c_62])).
% 1.85/1.30  tff(c_24, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.85/1.30  tff(c_71, plain, (![C_31, A_32, B_33]: (v1_partfun1(C_31, A_32) | ~v1_funct_2(C_31, A_32, B_33) | ~v1_funct_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | v1_xboole_0(B_33))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.85/1.30  tff(c_74, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_71])).
% 1.85/1.30  tff(c_77, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_74])).
% 1.85/1.30  tff(c_78, plain, (v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_63, c_77])).
% 1.85/1.30  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.85/1.30  tff(c_81, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_78, c_2])).
% 1.85/1.30  tff(c_85, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27, c_81])).
% 1.85/1.30  tff(c_86, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_20])).
% 1.85/1.30  tff(c_87, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_20])).
% 1.85/1.30  tff(c_92, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_87])).
% 1.85/1.30  tff(c_93, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_22])).
% 1.85/1.30  tff(c_160, plain, (![C_51, A_52, B_53]: (k3_partfun1(C_51, A_52, B_53)=C_51 | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_funct_1(C_51))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.85/1.30  tff(c_163, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_1')='#skF_3' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_93, c_160])).
% 1.85/1.30  tff(c_166, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_163])).
% 1.85/1.30  tff(c_110, plain, (k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_3', '#skF_1', '#skF_1'))!=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_92, c_18])).
% 1.85/1.30  tff(c_167, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_3')!=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_110])).
% 1.85/1.30  tff(c_117, plain, (![C_39, A_40, B_41]: (k3_partfun1(C_39, A_40, B_41)=C_39 | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_1(C_39))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.85/1.30  tff(c_120, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_1')='#skF_3' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_93, c_117])).
% 1.85/1.30  tff(c_123, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_120])).
% 1.85/1.30  tff(c_124, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_3')!=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_110])).
% 1.85/1.30  tff(c_136, plain, (![A_45, B_46, C_47]: (k5_partfun1(A_45, B_46, C_47)=k1_tarski(C_47) | ~v1_partfun1(C_47, A_45) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_1(C_47))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.30  tff(c_139, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_3')=k1_tarski('#skF_3') | ~v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_93, c_136])).
% 1.85/1.30  tff(c_142, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_3')=k1_tarski('#skF_3') | ~v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_139])).
% 1.85/1.30  tff(c_143, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_124, c_142])).
% 1.85/1.30  tff(c_111, plain, (![C_36, A_37, B_38]: (v1_partfun1(C_36, A_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.85/1.30  tff(c_115, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_93, c_111])).
% 1.85/1.30  tff(c_116, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_115])).
% 1.85/1.30  tff(c_94, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_24])).
% 1.85/1.30  tff(c_144, plain, (![C_48, A_49, B_50]: (v1_partfun1(C_48, A_49) | ~v1_funct_2(C_48, A_49, B_50) | ~v1_funct_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | v1_xboole_0(B_50))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.85/1.30  tff(c_147, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_93, c_144])).
% 1.85/1.30  tff(c_150, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_94, c_147])).
% 1.85/1.30  tff(c_151, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_116, c_150])).
% 1.85/1.30  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_151])).
% 1.85/1.30  tff(c_153, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_115])).
% 1.85/1.30  tff(c_179, plain, (![A_57, B_58, C_59]: (k5_partfun1(A_57, B_58, C_59)=k1_tarski(C_59) | ~v1_partfun1(C_59, A_57) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~v1_funct_1(C_59))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.30  tff(c_182, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_3')=k1_tarski('#skF_3') | ~v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_93, c_179])).
% 1.85/1.30  tff(c_185, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_3')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_153, c_182])).
% 1.85/1.30  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_185])).
% 1.85/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.30  
% 1.85/1.30  Inference rules
% 1.85/1.30  ----------------------
% 1.85/1.30  #Ref     : 0
% 1.85/1.30  #Sup     : 29
% 1.85/1.30  #Fact    : 0
% 1.85/1.30  #Define  : 0
% 1.85/1.30  #Split   : 3
% 1.85/1.30  #Chain   : 0
% 1.85/1.30  #Close   : 0
% 1.85/1.30  
% 1.85/1.30  Ordering : KBO
% 1.85/1.30  
% 1.85/1.30  Simplification rules
% 1.85/1.30  ----------------------
% 1.85/1.30  #Subsume      : 3
% 1.85/1.30  #Demod        : 24
% 1.85/1.30  #Tautology    : 16
% 1.85/1.30  #SimpNegUnit  : 7
% 1.85/1.30  #BackRed      : 5
% 1.85/1.30  
% 1.85/1.30  #Partial instantiations: 0
% 1.85/1.30  #Strategies tried      : 1
% 1.85/1.30  
% 1.85/1.30  Timing (in seconds)
% 1.85/1.30  ----------------------
% 1.85/1.30  Preprocessing        : 0.30
% 1.85/1.30  Parsing              : 0.16
% 1.85/1.30  CNF conversion       : 0.02
% 1.85/1.30  Main loop            : 0.15
% 1.85/1.30  Inferencing          : 0.06
% 1.85/1.30  Reduction            : 0.05
% 1.85/1.30  Demodulation         : 0.03
% 1.85/1.30  BG Simplification    : 0.01
% 1.85/1.30  Subsumption          : 0.02
% 1.85/1.30  Abstraction          : 0.01
% 1.85/1.30  MUC search           : 0.00
% 1.85/1.30  Cooper               : 0.00
% 1.85/1.30  Total                : 0.49
% 1.85/1.30  Index Insertion      : 0.00
% 1.85/1.30  Index Deletion       : 0.00
% 1.85/1.30  Index Matching       : 0.00
% 1.85/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
