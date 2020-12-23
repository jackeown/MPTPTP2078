%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:44 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 673 expanded)
%              Number of leaves         :   26 ( 225 expanded)
%              Depth                    :   13
%              Number of atoms          :  119 (1582 expanded)
%              Number of equality atoms :   47 ( 427 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_80,axiom,(
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

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_42,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34])).

tff(c_36,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_215,plain,(
    ! [B_56,C_57,A_58] :
      ( k1_xboole_0 = B_56
      | v1_funct_2(C_57,A_58,B_56)
      | k1_relset_1(A_58,B_56,C_57) != A_58
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_218,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_215])).

tff(c_231,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_218])).

tff(c_232,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_231])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_79,plain,(
    ! [B_25,A_26] :
      ( v1_xboole_0(B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_26))
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_87,plain,(
    ! [A_8] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_79])).

tff(c_88,plain,(
    ! [A_8] : ~ v1_xboole_0(A_8) ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( ~ r1_xboole_0(B_5,A_4)
      | ~ r1_tarski(B_5,A_4)
      | v1_xboole_0(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_104,plain,(
    ! [B_30,A_31] :
      ( ~ r1_xboole_0(B_30,A_31)
      | ~ r1_tarski(B_30,A_31) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_8])).

tff(c_109,plain,(
    ! [A_32] : ~ r1_tarski(A_32,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_114,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_4,c_109])).

tff(c_115,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_245,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_115])).

tff(c_12,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_248,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_232,c_12])).

tff(c_86,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_79])).

tff(c_121,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_264,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_121])).

tff(c_268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_264])).

tff(c_270,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_269,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_274,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_269,c_2])).

tff(c_302,plain,(
    ! [A_66] :
      ( A_66 = '#skF_3'
      | ~ v1_xboole_0(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_2])).

tff(c_309,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_270,c_302])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( k1_xboole_0 = B_7
      | k1_xboole_0 = A_6
      | k2_zfmisc_1(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_349,plain,(
    ! [B_71,A_72] :
      ( B_71 = '#skF_3'
      | A_72 = '#skF_3'
      | k2_zfmisc_1(A_72,B_71) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_274,c_274,c_10])).

tff(c_359,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_349])).

tff(c_364,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_359])).

tff(c_377,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_36])).

tff(c_279,plain,(
    ! [A_8] : m1_subset_1('#skF_3',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_16])).

tff(c_369,plain,(
    ! [A_8] : m1_subset_1('#skF_1',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_279])).

tff(c_375,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_274])).

tff(c_14,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [C_17,B_16] :
      ( v1_funct_2(C_17,k1_xboole_0,B_16)
      | k1_relset_1(k1_xboole_0,B_16,C_17) != k1_xboole_0
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_45,plain,(
    ! [C_17,B_16] :
      ( v1_funct_2(C_17,k1_xboole_0,B_16)
      | k1_relset_1(k1_xboole_0,B_16,C_17) != k1_xboole_0
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_480,plain,(
    ! [C_93,B_94] :
      ( v1_funct_2(C_93,'#skF_1',B_94)
      | k1_relset_1('#skF_1',B_94,C_93) != '#skF_1'
      | ~ m1_subset_1(C_93,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_375,c_375,c_375,c_45])).

tff(c_485,plain,(
    ! [B_95] :
      ( v1_funct_2('#skF_1','#skF_1',B_95)
      | k1_relset_1('#skF_1',B_95,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_369,c_480])).

tff(c_378,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_42])).

tff(c_488,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_485,c_378])).

tff(c_495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_488])).

tff(c_497,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_359])).

tff(c_22,plain,(
    ! [A_15] :
      ( v1_funct_2(k1_xboole_0,A_15,k1_xboole_0)
      | k1_xboole_0 = A_15
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_15,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    ! [A_15] :
      ( v1_funct_2(k1_xboole_0,A_15,k1_xboole_0)
      | k1_xboole_0 = A_15 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22])).

tff(c_276,plain,(
    ! [A_15] :
      ( v1_funct_2('#skF_3',A_15,'#skF_3')
      | A_15 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_274,c_274,c_44])).

tff(c_496,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_359])).

tff(c_500,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_42])).

tff(c_512,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_276,c_500])).

tff(c_516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_497,c_512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.46  
% 2.27/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.46  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.27/1.46  
% 2.27/1.46  %Foreground sorts:
% 2.27/1.46  
% 2.27/1.46  
% 2.27/1.46  %Background operators:
% 2.27/1.46  
% 2.27/1.46  
% 2.27/1.46  %Foreground operators:
% 2.27/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.27/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.27/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.27/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.27/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.46  
% 2.62/1.48  tff(f_93, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 2.62/1.48  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.62/1.48  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.62/1.48  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.62/1.48  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.62/1.48  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.62/1.48  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.62/1.48  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.62/1.48  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.62/1.48  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.48  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.48  tff(c_34, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.48  tff(c_42, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34])).
% 2.62/1.48  tff(c_36, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.48  tff(c_215, plain, (![B_56, C_57, A_58]: (k1_xboole_0=B_56 | v1_funct_2(C_57, A_58, B_56) | k1_relset_1(A_58, B_56, C_57)!=A_58 | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_56))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.62/1.48  tff(c_218, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_38, c_215])).
% 2.62/1.48  tff(c_231, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_218])).
% 2.62/1.48  tff(c_232, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_42, c_231])).
% 2.62/1.48  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.62/1.48  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.62/1.48  tff(c_16, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.62/1.48  tff(c_79, plain, (![B_25, A_26]: (v1_xboole_0(B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(A_26)) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.62/1.48  tff(c_87, plain, (![A_8]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_8))), inference(resolution, [status(thm)], [c_16, c_79])).
% 2.62/1.48  tff(c_88, plain, (![A_8]: (~v1_xboole_0(A_8))), inference(splitLeft, [status(thm)], [c_87])).
% 2.62/1.48  tff(c_8, plain, (![B_5, A_4]: (~r1_xboole_0(B_5, A_4) | ~r1_tarski(B_5, A_4) | v1_xboole_0(B_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.62/1.48  tff(c_104, plain, (![B_30, A_31]: (~r1_xboole_0(B_30, A_31) | ~r1_tarski(B_30, A_31))), inference(negUnitSimplification, [status(thm)], [c_88, c_8])).
% 2.62/1.48  tff(c_109, plain, (![A_32]: (~r1_tarski(A_32, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_104])).
% 2.62/1.48  tff(c_114, plain, $false, inference(resolution, [status(thm)], [c_4, c_109])).
% 2.62/1.48  tff(c_115, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_87])).
% 2.62/1.48  tff(c_245, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_232, c_115])).
% 2.62/1.48  tff(c_12, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.62/1.48  tff(c_248, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_232, c_232, c_12])).
% 2.62/1.48  tff(c_86, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_79])).
% 2.62/1.48  tff(c_121, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_86])).
% 2.62/1.48  tff(c_264, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_248, c_121])).
% 2.62/1.48  tff(c_268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_245, c_264])).
% 2.62/1.48  tff(c_270, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_86])).
% 2.62/1.48  tff(c_269, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_86])).
% 2.62/1.48  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.62/1.48  tff(c_274, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_269, c_2])).
% 2.62/1.48  tff(c_302, plain, (![A_66]: (A_66='#skF_3' | ~v1_xboole_0(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_2])).
% 2.62/1.48  tff(c_309, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_270, c_302])).
% 2.62/1.48  tff(c_10, plain, (![B_7, A_6]: (k1_xboole_0=B_7 | k1_xboole_0=A_6 | k2_zfmisc_1(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.62/1.48  tff(c_349, plain, (![B_71, A_72]: (B_71='#skF_3' | A_72='#skF_3' | k2_zfmisc_1(A_72, B_71)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_274, c_274, c_274, c_10])).
% 2.62/1.48  tff(c_359, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_309, c_349])).
% 2.62/1.48  tff(c_364, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_359])).
% 2.62/1.48  tff(c_377, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_364, c_36])).
% 2.62/1.48  tff(c_279, plain, (![A_8]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_16])).
% 2.62/1.48  tff(c_369, plain, (![A_8]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_364, c_279])).
% 2.62/1.48  tff(c_375, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_364, c_274])).
% 2.62/1.48  tff(c_14, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.62/1.48  tff(c_26, plain, (![C_17, B_16]: (v1_funct_2(C_17, k1_xboole_0, B_16) | k1_relset_1(k1_xboole_0, B_16, C_17)!=k1_xboole_0 | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_16))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.62/1.48  tff(c_45, plain, (![C_17, B_16]: (v1_funct_2(C_17, k1_xboole_0, B_16) | k1_relset_1(k1_xboole_0, B_16, C_17)!=k1_xboole_0 | ~m1_subset_1(C_17, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_26])).
% 2.62/1.48  tff(c_480, plain, (![C_93, B_94]: (v1_funct_2(C_93, '#skF_1', B_94) | k1_relset_1('#skF_1', B_94, C_93)!='#skF_1' | ~m1_subset_1(C_93, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_375, c_375, c_375, c_375, c_45])).
% 2.62/1.48  tff(c_485, plain, (![B_95]: (v1_funct_2('#skF_1', '#skF_1', B_95) | k1_relset_1('#skF_1', B_95, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_369, c_480])).
% 2.62/1.48  tff(c_378, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_364, c_42])).
% 2.62/1.48  tff(c_488, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_485, c_378])).
% 2.62/1.48  tff(c_495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_377, c_488])).
% 2.62/1.48  tff(c_497, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_359])).
% 2.62/1.48  tff(c_22, plain, (![A_15]: (v1_funct_2(k1_xboole_0, A_15, k1_xboole_0) | k1_xboole_0=A_15 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_15, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.62/1.48  tff(c_44, plain, (![A_15]: (v1_funct_2(k1_xboole_0, A_15, k1_xboole_0) | k1_xboole_0=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22])).
% 2.62/1.48  tff(c_276, plain, (![A_15]: (v1_funct_2('#skF_3', A_15, '#skF_3') | A_15='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_274, c_274, c_274, c_44])).
% 2.62/1.48  tff(c_496, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_359])).
% 2.62/1.48  tff(c_500, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_496, c_42])).
% 2.62/1.48  tff(c_512, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_276, c_500])).
% 2.62/1.48  tff(c_516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_497, c_512])).
% 2.62/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.48  
% 2.62/1.48  Inference rules
% 2.62/1.48  ----------------------
% 2.62/1.48  #Ref     : 0
% 2.62/1.48  #Sup     : 89
% 2.62/1.48  #Fact    : 0
% 2.62/1.48  #Define  : 0
% 2.62/1.48  #Split   : 3
% 2.62/1.48  #Chain   : 0
% 2.62/1.48  #Close   : 0
% 2.62/1.48  
% 2.62/1.48  Ordering : KBO
% 2.62/1.48  
% 2.62/1.48  Simplification rules
% 2.62/1.48  ----------------------
% 2.62/1.48  #Subsume      : 7
% 2.62/1.48  #Demod        : 116
% 2.62/1.48  #Tautology    : 67
% 2.62/1.48  #SimpNegUnit  : 5
% 2.62/1.48  #BackRed      : 48
% 2.62/1.48  
% 2.62/1.48  #Partial instantiations: 0
% 2.62/1.48  #Strategies tried      : 1
% 2.62/1.48  
% 2.62/1.48  Timing (in seconds)
% 2.62/1.48  ----------------------
% 2.67/1.48  Preprocessing        : 0.33
% 2.67/1.48  Parsing              : 0.18
% 2.67/1.48  CNF conversion       : 0.02
% 2.67/1.48  Main loop            : 0.26
% 2.67/1.48  Inferencing          : 0.09
% 2.67/1.48  Reduction            : 0.08
% 2.67/1.48  Demodulation         : 0.06
% 2.67/1.48  BG Simplification    : 0.02
% 2.67/1.48  Subsumption          : 0.05
% 2.67/1.48  Abstraction          : 0.01
% 2.67/1.48  MUC search           : 0.00
% 2.67/1.48  Cooper               : 0.00
% 2.67/1.48  Total                : 0.63
% 2.67/1.48  Index Insertion      : 0.00
% 2.67/1.48  Index Deletion       : 0.00
% 2.67/1.48  Index Matching       : 0.00
% 2.67/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
