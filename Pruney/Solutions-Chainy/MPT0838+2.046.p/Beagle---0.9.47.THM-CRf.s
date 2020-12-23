%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:15 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 246 expanded)
%              Number of leaves         :   38 (  97 expanded)
%              Depth                    :    8
%              Number of atoms          :  127 ( 514 expanded)
%              Number of equality atoms :   45 ( 152 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_61,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_81,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_22,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_175,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_182,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_48,c_175])).

tff(c_186,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_182])).

tff(c_24,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) != k1_xboole_0
      | k1_xboole_0 = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_193,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_186,c_24])).

tff(c_733,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_196,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_239,plain,(
    ! [C_83,B_84,A_85] :
      ( v5_relat_1(C_83,B_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_253,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_239])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_272,plain,(
    ! [C_93,B_94,A_95] :
      ( r2_hidden(C_93,B_94)
      | ~ r2_hidden(C_93,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_299,plain,(
    ! [A_99,B_100] :
      ( r2_hidden('#skF_1'(A_99),B_100)
      | ~ r1_tarski(A_99,B_100)
      | v1_xboole_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_4,c_272])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_395,plain,(
    ! [A_113,B_114] :
      ( m1_subset_1('#skF_1'(A_113),B_114)
      | ~ r1_tarski(A_113,B_114)
      | v1_xboole_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_299,c_14])).

tff(c_331,plain,(
    ! [A_107,B_108,C_109] :
      ( k2_relset_1(A_107,B_108,C_109) = k2_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_345,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_331])).

tff(c_124,plain,(
    ! [D_63] :
      ( ~ r2_hidden(D_63,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(D_63,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_129,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6')),'#skF_5')
    | v1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_4,c_124])).

tff(c_195,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_347,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_195])).

tff(c_419,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_395,c_347])).

tff(c_425,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_419])).

tff(c_428,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_425])).

tff(c_435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_253,c_428])).

tff(c_436,plain,(
    v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_442,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_436,c_12])).

tff(c_449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_442])).

tff(c_450,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_46,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_472,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_46])).

tff(c_30,plain,(
    ! [A_21] : k1_relat_1('#skF_3'(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ! [A_21] : v1_relat_1('#skF_3'(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_78,plain,(
    ! [A_60] :
      ( k1_relat_1(A_60) != k1_xboole_0
      | k1_xboole_0 = A_60
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_84,plain,(
    ! [A_21] :
      ( k1_relat_1('#skF_3'(A_21)) != k1_xboole_0
      | '#skF_3'(A_21) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_78])).

tff(c_89,plain,(
    ! [A_61] :
      ( k1_xboole_0 != A_61
      | '#skF_3'(A_61) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_84])).

tff(c_95,plain,(
    ! [A_61] :
      ( k1_relat_1(k1_xboole_0) = A_61
      | k1_xboole_0 != A_61 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_30])).

tff(c_505,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_450,c_95])).

tff(c_709,plain,(
    ! [A_154,B_155,C_156] :
      ( k1_relset_1(A_154,B_155,C_156) = k1_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_720,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_709])).

tff(c_724,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_720])).

tff(c_726,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_472,c_724])).

tff(c_727,plain,(
    v1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_732,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_727,c_12])).

tff(c_997,plain,(
    ! [A_204,B_205,C_206] :
      ( k2_relset_1(A_204,B_205,C_206) = k2_relat_1(C_206)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1012,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_997])).

tff(c_1017,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_732,c_1012])).

tff(c_1019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_733,c_1017])).

tff(c_1020,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_1029,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1020,c_46])).

tff(c_1085,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1020,c_1020,c_95])).

tff(c_1403,plain,(
    ! [A_258,B_259,C_260] :
      ( k1_relset_1(A_258,B_259,C_260) = k1_relat_1(C_260)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1418,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_1403])).

tff(c_1423,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_1418])).

tff(c_1425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1029,c_1423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.55  
% 3.32/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.55  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2
% 3.40/1.55  
% 3.40/1.55  %Foreground sorts:
% 3.40/1.55  
% 3.40/1.55  
% 3.40/1.55  %Background operators:
% 3.40/1.55  
% 3.40/1.55  
% 3.40/1.55  %Foreground operators:
% 3.40/1.55  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.40/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.40/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.40/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.40/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.40/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.40/1.55  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.40/1.55  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.40/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.40/1.55  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.40/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.40/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.40/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.40/1.55  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.40/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.40/1.55  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.40/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.40/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.40/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.40/1.55  
% 3.40/1.57  tff(f_61, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.40/1.57  tff(f_116, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 3.40/1.57  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.40/1.57  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.40/1.57  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.40/1.57  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.40/1.57  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.40/1.57  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.40/1.57  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.40/1.57  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.40/1.57  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.40/1.57  tff(f_81, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e9_44_1__funct_1)).
% 3.40/1.57  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.40/1.57  tff(c_22, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.40/1.57  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.40/1.57  tff(c_175, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.40/1.57  tff(c_182, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_175])).
% 3.40/1.57  tff(c_186, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_182])).
% 3.40/1.57  tff(c_24, plain, (![A_20]: (k2_relat_1(A_20)!=k1_xboole_0 | k1_xboole_0=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.40/1.57  tff(c_193, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_186, c_24])).
% 3.40/1.57  tff(c_733, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_193])).
% 3.40/1.57  tff(c_196, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_193])).
% 3.40/1.57  tff(c_239, plain, (![C_83, B_84, A_85]: (v5_relat_1(C_83, B_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.40/1.57  tff(c_253, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_239])).
% 3.40/1.57  tff(c_20, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.40/1.57  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.57  tff(c_272, plain, (![C_93, B_94, A_95]: (r2_hidden(C_93, B_94) | ~r2_hidden(C_93, A_95) | ~r1_tarski(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.40/1.57  tff(c_299, plain, (![A_99, B_100]: (r2_hidden('#skF_1'(A_99), B_100) | ~r1_tarski(A_99, B_100) | v1_xboole_0(A_99))), inference(resolution, [status(thm)], [c_4, c_272])).
% 3.40/1.57  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.40/1.57  tff(c_395, plain, (![A_113, B_114]: (m1_subset_1('#skF_1'(A_113), B_114) | ~r1_tarski(A_113, B_114) | v1_xboole_0(A_113))), inference(resolution, [status(thm)], [c_299, c_14])).
% 3.40/1.57  tff(c_331, plain, (![A_107, B_108, C_109]: (k2_relset_1(A_107, B_108, C_109)=k2_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.40/1.57  tff(c_345, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_331])).
% 3.40/1.57  tff(c_124, plain, (![D_63]: (~r2_hidden(D_63, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(D_63, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.40/1.57  tff(c_129, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6')), '#skF_5') | v1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_4, c_124])).
% 3.40/1.57  tff(c_195, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(splitLeft, [status(thm)], [c_129])).
% 3.40/1.57  tff(c_347, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_345, c_195])).
% 3.40/1.57  tff(c_419, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | v1_xboole_0(k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_395, c_347])).
% 3.40/1.57  tff(c_425, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_419])).
% 3.40/1.57  tff(c_428, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_425])).
% 3.40/1.57  tff(c_435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_186, c_253, c_428])).
% 3.40/1.57  tff(c_436, plain, (v1_xboole_0(k2_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_419])).
% 3.40/1.57  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.40/1.57  tff(c_442, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_436, c_12])).
% 3.40/1.57  tff(c_449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_442])).
% 3.40/1.57  tff(c_450, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_193])).
% 3.40/1.57  tff(c_46, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.40/1.57  tff(c_472, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_450, c_46])).
% 3.40/1.57  tff(c_30, plain, (![A_21]: (k1_relat_1('#skF_3'(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.40/1.57  tff(c_34, plain, (![A_21]: (v1_relat_1('#skF_3'(A_21)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.40/1.57  tff(c_78, plain, (![A_60]: (k1_relat_1(A_60)!=k1_xboole_0 | k1_xboole_0=A_60 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.40/1.57  tff(c_84, plain, (![A_21]: (k1_relat_1('#skF_3'(A_21))!=k1_xboole_0 | '#skF_3'(A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_78])).
% 3.40/1.57  tff(c_89, plain, (![A_61]: (k1_xboole_0!=A_61 | '#skF_3'(A_61)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_84])).
% 3.40/1.57  tff(c_95, plain, (![A_61]: (k1_relat_1(k1_xboole_0)=A_61 | k1_xboole_0!=A_61)), inference(superposition, [status(thm), theory('equality')], [c_89, c_30])).
% 3.40/1.57  tff(c_505, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_450, c_450, c_95])).
% 3.40/1.57  tff(c_709, plain, (![A_154, B_155, C_156]: (k1_relset_1(A_154, B_155, C_156)=k1_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.40/1.57  tff(c_720, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_709])).
% 3.40/1.57  tff(c_724, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_505, c_720])).
% 3.40/1.57  tff(c_726, plain, $false, inference(negUnitSimplification, [status(thm)], [c_472, c_724])).
% 3.40/1.57  tff(c_727, plain, (v1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_129])).
% 3.40/1.57  tff(c_732, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_727, c_12])).
% 3.40/1.57  tff(c_997, plain, (![A_204, B_205, C_206]: (k2_relset_1(A_204, B_205, C_206)=k2_relat_1(C_206) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.40/1.57  tff(c_1012, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_997])).
% 3.40/1.57  tff(c_1017, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_732, c_1012])).
% 3.40/1.57  tff(c_1019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_733, c_1017])).
% 3.40/1.57  tff(c_1020, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_193])).
% 3.40/1.57  tff(c_1029, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1020, c_46])).
% 3.40/1.57  tff(c_1085, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1020, c_1020, c_95])).
% 3.40/1.57  tff(c_1403, plain, (![A_258, B_259, C_260]: (k1_relset_1(A_258, B_259, C_260)=k1_relat_1(C_260) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.40/1.57  tff(c_1418, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_1403])).
% 3.40/1.57  tff(c_1423, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_1418])).
% 3.40/1.57  tff(c_1425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1029, c_1423])).
% 3.40/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.57  
% 3.40/1.57  Inference rules
% 3.40/1.57  ----------------------
% 3.40/1.57  #Ref     : 5
% 3.40/1.57  #Sup     : 261
% 3.40/1.57  #Fact    : 0
% 3.40/1.57  #Define  : 0
% 3.40/1.57  #Split   : 9
% 3.40/1.57  #Chain   : 0
% 3.40/1.57  #Close   : 0
% 3.40/1.57  
% 3.40/1.57  Ordering : KBO
% 3.40/1.57  
% 3.40/1.57  Simplification rules
% 3.40/1.57  ----------------------
% 3.40/1.57  #Subsume      : 26
% 3.40/1.57  #Demod        : 127
% 3.40/1.57  #Tautology    : 96
% 3.40/1.57  #SimpNegUnit  : 15
% 3.40/1.57  #BackRed      : 35
% 3.40/1.57  
% 3.40/1.57  #Partial instantiations: 0
% 3.40/1.57  #Strategies tried      : 1
% 3.40/1.57  
% 3.40/1.57  Timing (in seconds)
% 3.40/1.57  ----------------------
% 3.40/1.57  Preprocessing        : 0.31
% 3.40/1.57  Parsing              : 0.16
% 3.40/1.57  CNF conversion       : 0.02
% 3.40/1.57  Main loop            : 0.44
% 3.40/1.57  Inferencing          : 0.17
% 3.40/1.57  Reduction            : 0.13
% 3.40/1.57  Demodulation         : 0.09
% 3.40/1.57  BG Simplification    : 0.02
% 3.40/1.57  Subsumption          : 0.07
% 3.40/1.57  Abstraction          : 0.02
% 3.40/1.57  MUC search           : 0.00
% 3.40/1.57  Cooper               : 0.00
% 3.40/1.57  Total                : 0.78
% 3.40/1.57  Index Insertion      : 0.00
% 3.40/1.57  Index Deletion       : 0.00
% 3.40/1.57  Index Matching       : 0.00
% 3.40/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
