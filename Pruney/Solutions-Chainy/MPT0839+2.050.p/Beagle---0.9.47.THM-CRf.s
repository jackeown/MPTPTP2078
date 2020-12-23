%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:28 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 166 expanded)
%              Number of leaves         :   33 (  69 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 328 expanded)
%              Number of equality atoms :   36 (  87 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_34,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_18,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_61,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_61])).

tff(c_72,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_68])).

tff(c_20,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) = k1_xboole_0
      | k2_relat_1(A_17) != k1_xboole_0
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_76,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_20])).

tff(c_77,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_78,plain,(
    ! [A_51] :
      ( k2_relat_1(A_51) = k1_xboole_0
      | k1_relat_1(A_51) != k1_xboole_0
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_81,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_78])).

tff(c_87,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_81])).

tff(c_127,plain,(
    ! [C_60,A_61,B_62] :
      ( v4_relat_1(C_60,A_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_141,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_127])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_319,plain,(
    ! [A_95,B_96,C_97] :
      ( k1_relset_1(A_95,B_96,C_97) = k1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_343,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_319])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_142,plain,(
    ! [C_63,B_64,A_65] :
      ( r2_hidden(C_63,B_64)
      | ~ r2_hidden(C_63,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_162,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_2'(A_72),B_73)
      | ~ r1_tarski(A_72,B_73)
      | k1_xboole_0 = A_72 ) ),
    inference(resolution,[status(thm)],[c_8,c_142])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_184,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1('#skF_2'(A_75),B_76)
      | ~ r1_tarski(A_75,B_76)
      | k1_xboole_0 = A_75 ) ),
    inference(resolution,[status(thm)],[c_162,c_10])).

tff(c_50,plain,(
    ! [D_47] :
      ( ~ r2_hidden(D_47,k1_relset_1('#skF_4','#skF_3','#skF_5'))
      | ~ m1_subset_1(D_47,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_55,plain,
    ( ~ m1_subset_1('#skF_2'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4')
    | k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_50])).

tff(c_105,plain,(
    ~ m1_subset_1('#skF_2'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_202,plain,
    ( ~ r1_tarski(k1_relset_1('#skF_4','#skF_3','#skF_5'),'#skF_4')
    | k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_184,c_105])).

tff(c_318,plain,(
    ~ r1_tarski(k1_relset_1('#skF_4','#skF_3','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_344,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_318])).

tff(c_355,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_344])).

tff(c_359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_141,c_355])).

tff(c_360,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_416,plain,(
    ! [A_101,B_102,C_103] :
      ( k1_relset_1(A_101,B_102,C_103) = k1_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_435,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_416])).

tff(c_441,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_435])).

tff(c_443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_441])).

tff(c_444,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_578,plain,(
    ! [A_128,B_129,C_130] :
      ( k1_relset_1(A_128,B_129,C_130) = k1_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_593,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_578])).

tff(c_598,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_593])).

tff(c_600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_598])).

tff(c_602,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_728,plain,(
    ! [A_154,B_155,C_156] :
      ( k2_relset_1(A_154,B_155,C_156) = k2_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_739,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_728])).

tff(c_743,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_739])).

tff(c_745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_743])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:52:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.44  
% 2.87/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.44  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.87/1.44  
% 2.87/1.44  %Foreground sorts:
% 2.87/1.44  
% 2.87/1.44  
% 2.87/1.44  %Background operators:
% 2.87/1.44  
% 2.87/1.44  
% 2.87/1.44  %Foreground operators:
% 2.87/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.87/1.44  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.87/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.87/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.87/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.87/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.87/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.87/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.87/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.87/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.44  
% 2.87/1.45  tff(f_100, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 2.87/1.45  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.87/1.45  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.87/1.45  tff(f_65, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.87/1.45  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.87/1.45  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.87/1.46  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.87/1.46  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.87/1.46  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.87/1.46  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.87/1.46  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.87/1.46  tff(c_34, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.87/1.46  tff(c_18, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.87/1.46  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.87/1.46  tff(c_61, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.87/1.46  tff(c_68, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_61])).
% 2.87/1.46  tff(c_72, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_68])).
% 2.87/1.46  tff(c_20, plain, (![A_17]: (k1_relat_1(A_17)=k1_xboole_0 | k2_relat_1(A_17)!=k1_xboole_0 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.87/1.46  tff(c_76, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_20])).
% 2.87/1.46  tff(c_77, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_76])).
% 2.87/1.46  tff(c_78, plain, (![A_51]: (k2_relat_1(A_51)=k1_xboole_0 | k1_relat_1(A_51)!=k1_xboole_0 | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.87/1.46  tff(c_81, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_78])).
% 2.87/1.46  tff(c_87, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_77, c_81])).
% 2.87/1.46  tff(c_127, plain, (![C_60, A_61, B_62]: (v4_relat_1(C_60, A_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.87/1.46  tff(c_141, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_127])).
% 2.87/1.46  tff(c_16, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(B_14), A_13) | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.87/1.46  tff(c_319, plain, (![A_95, B_96, C_97]: (k1_relset_1(A_95, B_96, C_97)=k1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.87/1.46  tff(c_343, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_319])).
% 2.87/1.46  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.87/1.46  tff(c_142, plain, (![C_63, B_64, A_65]: (r2_hidden(C_63, B_64) | ~r2_hidden(C_63, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.46  tff(c_162, plain, (![A_72, B_73]: (r2_hidden('#skF_2'(A_72), B_73) | ~r1_tarski(A_72, B_73) | k1_xboole_0=A_72)), inference(resolution, [status(thm)], [c_8, c_142])).
% 2.87/1.46  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.87/1.46  tff(c_184, plain, (![A_75, B_76]: (m1_subset_1('#skF_2'(A_75), B_76) | ~r1_tarski(A_75, B_76) | k1_xboole_0=A_75)), inference(resolution, [status(thm)], [c_162, c_10])).
% 2.87/1.46  tff(c_50, plain, (![D_47]: (~r2_hidden(D_47, k1_relset_1('#skF_4', '#skF_3', '#skF_5')) | ~m1_subset_1(D_47, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.87/1.46  tff(c_55, plain, (~m1_subset_1('#skF_2'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4') | k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_50])).
% 2.87/1.46  tff(c_105, plain, (~m1_subset_1('#skF_2'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_55])).
% 2.87/1.46  tff(c_202, plain, (~r1_tarski(k1_relset_1('#skF_4', '#skF_3', '#skF_5'), '#skF_4') | k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_184, c_105])).
% 2.87/1.46  tff(c_318, plain, (~r1_tarski(k1_relset_1('#skF_4', '#skF_3', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_202])).
% 2.87/1.46  tff(c_344, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_343, c_318])).
% 2.87/1.46  tff(c_355, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_344])).
% 2.87/1.46  tff(c_359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_141, c_355])).
% 2.87/1.46  tff(c_360, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_202])).
% 2.87/1.46  tff(c_416, plain, (![A_101, B_102, C_103]: (k1_relset_1(A_101, B_102, C_103)=k1_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.87/1.46  tff(c_435, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_416])).
% 2.87/1.46  tff(c_441, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_360, c_435])).
% 2.87/1.46  tff(c_443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_441])).
% 2.87/1.46  tff(c_444, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_55])).
% 2.87/1.46  tff(c_578, plain, (![A_128, B_129, C_130]: (k1_relset_1(A_128, B_129, C_130)=k1_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.87/1.46  tff(c_593, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_578])).
% 2.87/1.46  tff(c_598, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_444, c_593])).
% 2.87/1.46  tff(c_600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_598])).
% 2.87/1.46  tff(c_602, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_76])).
% 2.87/1.46  tff(c_728, plain, (![A_154, B_155, C_156]: (k2_relset_1(A_154, B_155, C_156)=k2_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.87/1.46  tff(c_739, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_728])).
% 2.87/1.46  tff(c_743, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_602, c_739])).
% 2.87/1.46  tff(c_745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_743])).
% 2.87/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.46  
% 2.87/1.46  Inference rules
% 2.87/1.46  ----------------------
% 2.87/1.46  #Ref     : 0
% 2.87/1.46  #Sup     : 136
% 2.87/1.46  #Fact    : 0
% 2.87/1.46  #Define  : 0
% 2.87/1.46  #Split   : 5
% 2.87/1.46  #Chain   : 0
% 2.87/1.46  #Close   : 0
% 2.87/1.46  
% 2.87/1.46  Ordering : KBO
% 2.87/1.46  
% 2.87/1.46  Simplification rules
% 2.87/1.46  ----------------------
% 2.87/1.46  #Subsume      : 4
% 2.87/1.46  #Demod        : 37
% 2.87/1.46  #Tautology    : 31
% 2.87/1.46  #SimpNegUnit  : 4
% 2.87/1.46  #BackRed      : 11
% 2.87/1.46  
% 2.87/1.46  #Partial instantiations: 0
% 2.87/1.46  #Strategies tried      : 1
% 2.87/1.46  
% 2.87/1.46  Timing (in seconds)
% 2.87/1.46  ----------------------
% 2.87/1.46  Preprocessing        : 0.32
% 2.87/1.46  Parsing              : 0.18
% 2.87/1.46  CNF conversion       : 0.02
% 2.87/1.46  Main loop            : 0.34
% 2.87/1.46  Inferencing          : 0.14
% 2.87/1.46  Reduction            : 0.09
% 2.87/1.46  Demodulation         : 0.06
% 2.87/1.46  BG Simplification    : 0.02
% 2.87/1.46  Subsumption          : 0.05
% 2.87/1.46  Abstraction          : 0.02
% 2.87/1.46  MUC search           : 0.00
% 2.87/1.46  Cooper               : 0.00
% 2.87/1.46  Total                : 0.69
% 2.87/1.46  Index Insertion      : 0.00
% 2.87/1.46  Index Deletion       : 0.00
% 2.87/1.46  Index Matching       : 0.00
% 2.87/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
