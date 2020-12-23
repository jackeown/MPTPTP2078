%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:10 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   73 (  83 expanded)
%              Number of leaves         :   43 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 132 expanded)
%              Number of equality atoms :   33 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

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
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

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

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_60,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_160,plain,(
    ! [C_78,B_79,A_80] :
      ( v5_relat_1(C_78,B_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_164,plain,(
    v5_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_160])).

tff(c_62,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_152,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_156,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_152])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_131,plain,(
    ! [A_69,B_70] :
      ( r2_hidden(A_69,B_70)
      | k4_xboole_0(k1_tarski(A_69),B_70) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_141,plain,(
    ! [A_72] :
      ( r2_hidden(A_72,k1_xboole_0)
      | k1_tarski(A_72) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_131])).

tff(c_38,plain,(
    ! [B_43,A_42] :
      ( ~ r1_tarski(B_43,A_42)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_147,plain,(
    ! [A_72] :
      ( ~ r1_tarski(k1_xboole_0,A_72)
      | k1_tarski(A_72) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_141,c_38])).

tff(c_151,plain,(
    ! [A_72] : k1_tarski(A_72) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_147])).

tff(c_66,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_190,plain,(
    ! [A_95,B_96,C_97] :
      ( k1_relset_1(A_95,B_96,C_97) = k1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_194,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_190])).

tff(c_390,plain,(
    ! [B_152,A_153,C_154] :
      ( k1_xboole_0 = B_152
      | k1_relset_1(A_153,B_152,C_154) = A_153
      | ~ v1_funct_2(C_154,A_153,B_152)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_153,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_393,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_390])).

tff(c_396,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_194,c_393])).

tff(c_397,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_396])).

tff(c_308,plain,(
    ! [B_127,C_128,A_129] :
      ( r2_hidden(k1_funct_1(B_127,C_128),A_129)
      | ~ r2_hidden(C_128,k1_relat_1(B_127))
      | ~ v1_funct_1(B_127)
      | ~ v5_relat_1(B_127,A_129)
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [C_7,A_3] :
      ( C_7 = A_3
      | ~ r2_hidden(C_7,k1_tarski(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_322,plain,(
    ! [B_127,C_128,A_3] :
      ( k1_funct_1(B_127,C_128) = A_3
      | ~ r2_hidden(C_128,k1_relat_1(B_127))
      | ~ v1_funct_1(B_127)
      | ~ v5_relat_1(B_127,k1_tarski(A_3))
      | ~ v1_relat_1(B_127) ) ),
    inference(resolution,[status(thm)],[c_308,c_6])).

tff(c_404,plain,(
    ! [C_128,A_3] :
      ( k1_funct_1('#skF_6',C_128) = A_3
      | ~ r2_hidden(C_128,'#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',k1_tarski(A_3))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_322])).

tff(c_422,plain,(
    ! [C_155,A_156] :
      ( k1_funct_1('#skF_6',C_155) = A_156
      | ~ r2_hidden(C_155,'#skF_3')
      | ~ v5_relat_1('#skF_6',k1_tarski(A_156)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_68,c_404])).

tff(c_438,plain,(
    ! [A_157] :
      ( k1_funct_1('#skF_6','#skF_5') = A_157
      | ~ v5_relat_1('#skF_6',k1_tarski(A_157)) ) ),
    inference(resolution,[status(thm)],[c_62,c_422])).

tff(c_441,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_164,c_438])).

tff(c_445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.40  
% 2.77/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.40  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.77/1.40  
% 2.77/1.40  %Foreground sorts:
% 2.77/1.40  
% 2.77/1.40  
% 2.77/1.40  %Background operators:
% 2.77/1.40  
% 2.77/1.40  
% 2.77/1.40  %Foreground operators:
% 2.77/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.77/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.77/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.77/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.77/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.77/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.77/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.77/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.77/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.77/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.77/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.77/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.77/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.77/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.40  
% 2.77/1.41  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.77/1.41  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.77/1.41  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.77/1.41  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.77/1.41  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.77/1.41  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.77/1.41  tff(f_70, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.77/1.41  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.77/1.41  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.77/1.41  tff(f_65, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 2.77/1.41  tff(f_36, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.77/1.41  tff(c_60, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.77/1.41  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.77/1.41  tff(c_160, plain, (![C_78, B_79, A_80]: (v5_relat_1(C_78, B_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.77/1.41  tff(c_164, plain, (v5_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_160])).
% 2.77/1.41  tff(c_62, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.77/1.41  tff(c_152, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.77/1.41  tff(c_156, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_152])).
% 2.77/1.41  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.77/1.41  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.77/1.41  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.77/1.41  tff(c_131, plain, (![A_69, B_70]: (r2_hidden(A_69, B_70) | k4_xboole_0(k1_tarski(A_69), B_70)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.77/1.41  tff(c_141, plain, (![A_72]: (r2_hidden(A_72, k1_xboole_0) | k1_tarski(A_72)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_131])).
% 2.77/1.41  tff(c_38, plain, (![B_43, A_42]: (~r1_tarski(B_43, A_42) | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.77/1.41  tff(c_147, plain, (![A_72]: (~r1_tarski(k1_xboole_0, A_72) | k1_tarski(A_72)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_141, c_38])).
% 2.77/1.41  tff(c_151, plain, (![A_72]: (k1_tarski(A_72)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_147])).
% 2.77/1.41  tff(c_66, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.77/1.41  tff(c_190, plain, (![A_95, B_96, C_97]: (k1_relset_1(A_95, B_96, C_97)=k1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.77/1.41  tff(c_194, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_190])).
% 2.77/1.41  tff(c_390, plain, (![B_152, A_153, C_154]: (k1_xboole_0=B_152 | k1_relset_1(A_153, B_152, C_154)=A_153 | ~v1_funct_2(C_154, A_153, B_152) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_153, B_152))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.77/1.41  tff(c_393, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_390])).
% 2.77/1.41  tff(c_396, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_194, c_393])).
% 2.77/1.41  tff(c_397, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_151, c_396])).
% 2.77/1.41  tff(c_308, plain, (![B_127, C_128, A_129]: (r2_hidden(k1_funct_1(B_127, C_128), A_129) | ~r2_hidden(C_128, k1_relat_1(B_127)) | ~v1_funct_1(B_127) | ~v5_relat_1(B_127, A_129) | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.77/1.41  tff(c_6, plain, (![C_7, A_3]: (C_7=A_3 | ~r2_hidden(C_7, k1_tarski(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.77/1.41  tff(c_322, plain, (![B_127, C_128, A_3]: (k1_funct_1(B_127, C_128)=A_3 | ~r2_hidden(C_128, k1_relat_1(B_127)) | ~v1_funct_1(B_127) | ~v5_relat_1(B_127, k1_tarski(A_3)) | ~v1_relat_1(B_127))), inference(resolution, [status(thm)], [c_308, c_6])).
% 2.77/1.41  tff(c_404, plain, (![C_128, A_3]: (k1_funct_1('#skF_6', C_128)=A_3 | ~r2_hidden(C_128, '#skF_3') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', k1_tarski(A_3)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_397, c_322])).
% 2.77/1.41  tff(c_422, plain, (![C_155, A_156]: (k1_funct_1('#skF_6', C_155)=A_156 | ~r2_hidden(C_155, '#skF_3') | ~v5_relat_1('#skF_6', k1_tarski(A_156)))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_68, c_404])).
% 2.77/1.41  tff(c_438, plain, (![A_157]: (k1_funct_1('#skF_6', '#skF_5')=A_157 | ~v5_relat_1('#skF_6', k1_tarski(A_157)))), inference(resolution, [status(thm)], [c_62, c_422])).
% 2.77/1.41  tff(c_441, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_164, c_438])).
% 2.77/1.41  tff(c_445, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_441])).
% 2.77/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.41  
% 2.77/1.41  Inference rules
% 2.77/1.41  ----------------------
% 2.77/1.41  #Ref     : 0
% 2.77/1.41  #Sup     : 78
% 2.77/1.41  #Fact    : 0
% 2.77/1.41  #Define  : 0
% 2.77/1.41  #Split   : 1
% 2.77/1.41  #Chain   : 0
% 2.77/1.41  #Close   : 0
% 2.77/1.41  
% 2.77/1.41  Ordering : KBO
% 2.77/1.41  
% 2.77/1.41  Simplification rules
% 2.77/1.41  ----------------------
% 2.77/1.41  #Subsume      : 11
% 2.77/1.41  #Demod        : 17
% 2.77/1.41  #Tautology    : 38
% 2.77/1.41  #SimpNegUnit  : 9
% 2.77/1.41  #BackRed      : 2
% 2.77/1.41  
% 2.77/1.41  #Partial instantiations: 0
% 2.77/1.41  #Strategies tried      : 1
% 2.77/1.41  
% 2.77/1.41  Timing (in seconds)
% 2.77/1.41  ----------------------
% 2.77/1.42  Preprocessing        : 0.36
% 2.77/1.42  Parsing              : 0.19
% 2.77/1.42  CNF conversion       : 0.03
% 2.77/1.42  Main loop            : 0.29
% 2.77/1.42  Inferencing          : 0.11
% 2.77/1.42  Reduction            : 0.08
% 2.77/1.42  Demodulation         : 0.06
% 2.77/1.42  BG Simplification    : 0.02
% 2.77/1.42  Subsumption          : 0.06
% 2.77/1.42  Abstraction          : 0.02
% 2.77/1.42  MUC search           : 0.00
% 2.77/1.42  Cooper               : 0.00
% 2.77/1.42  Total                : 0.68
% 2.77/1.42  Index Insertion      : 0.00
% 2.77/1.42  Index Deletion       : 0.00
% 2.77/1.42  Index Matching       : 0.00
% 2.77/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
