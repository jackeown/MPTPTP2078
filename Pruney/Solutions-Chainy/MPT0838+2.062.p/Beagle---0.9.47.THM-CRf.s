%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:18 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 119 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 222 expanded)
%              Number of equality atoms :   27 (  56 expanded)
%              Maximal formula depth    :   13 (   4 average)
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
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

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
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_34,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_18,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_61,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
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

tff(c_112,plain,(
    ! [C_57,B_58,A_59] :
      ( v5_relat_1(C_57,B_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_126,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_112])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

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

tff(c_174,plain,(
    ! [A_72,B_73] :
      ( m1_subset_1('#skF_2'(A_72),B_73)
      | ~ r1_tarski(A_72,B_73)
      | k1_xboole_0 = A_72 ) ),
    inference(resolution,[status(thm)],[c_162,c_10])).

tff(c_228,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(A_79,B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_247,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_228])).

tff(c_50,plain,(
    ! [D_47] :
      ( ~ r2_hidden(D_47,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_47,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_55,plain,
    ( ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_50])).

tff(c_105,plain,(
    ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_249,plain,(
    ~ m1_subset_1('#skF_2'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_105])).

tff(c_257,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_174,c_249])).

tff(c_260,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_257])).

tff(c_263,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_260])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_126,c_263])).

tff(c_268,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_359,plain,(
    ! [A_103,B_104,C_105] :
      ( k2_relset_1(A_103,B_104,C_105) = k2_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_370,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_359])).

tff(c_374,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_370])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_374])).

tff(c_377,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_565,plain,(
    ! [A_137,B_138,C_139] :
      ( k1_relset_1(A_137,B_138,C_139) = k1_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_576,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_565])).

tff(c_580,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_576])).

tff(c_582,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_580])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:40:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.51  
% 2.76/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.51  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.76/1.51  
% 2.76/1.51  %Foreground sorts:
% 2.76/1.51  
% 2.76/1.51  
% 2.76/1.51  %Background operators:
% 2.76/1.51  
% 2.76/1.51  
% 2.76/1.51  %Foreground operators:
% 2.76/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.76/1.51  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.76/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.76/1.51  tff('#skF_5', type, '#skF_5': $i).
% 2.76/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.76/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.76/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.76/1.51  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.76/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.76/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.76/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.51  
% 2.76/1.53  tff(f_100, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.76/1.53  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.76/1.53  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.76/1.53  tff(f_65, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.76/1.53  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.76/1.53  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.76/1.53  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.76/1.53  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.76/1.53  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.76/1.53  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.76/1.53  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.76/1.53  tff(c_34, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.76/1.53  tff(c_18, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.76/1.53  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.76/1.53  tff(c_61, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.76/1.53  tff(c_68, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_61])).
% 2.76/1.53  tff(c_72, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_68])).
% 2.76/1.53  tff(c_20, plain, (![A_17]: (k1_relat_1(A_17)=k1_xboole_0 | k2_relat_1(A_17)!=k1_xboole_0 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.76/1.53  tff(c_76, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_20])).
% 2.76/1.53  tff(c_77, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_76])).
% 2.76/1.53  tff(c_112, plain, (![C_57, B_58, A_59]: (v5_relat_1(C_57, B_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.76/1.53  tff(c_126, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_112])).
% 2.76/1.53  tff(c_16, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.76/1.53  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.53  tff(c_142, plain, (![C_63, B_64, A_65]: (r2_hidden(C_63, B_64) | ~r2_hidden(C_63, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.53  tff(c_162, plain, (![A_72, B_73]: (r2_hidden('#skF_2'(A_72), B_73) | ~r1_tarski(A_72, B_73) | k1_xboole_0=A_72)), inference(resolution, [status(thm)], [c_8, c_142])).
% 2.76/1.53  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.76/1.53  tff(c_174, plain, (![A_72, B_73]: (m1_subset_1('#skF_2'(A_72), B_73) | ~r1_tarski(A_72, B_73) | k1_xboole_0=A_72)), inference(resolution, [status(thm)], [c_162, c_10])).
% 2.76/1.53  tff(c_228, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.76/1.53  tff(c_247, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_228])).
% 2.76/1.53  tff(c_50, plain, (![D_47]: (~r2_hidden(D_47, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_47, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.76/1.53  tff(c_55, plain, (~m1_subset_1('#skF_2'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_50])).
% 2.76/1.53  tff(c_105, plain, (~m1_subset_1('#skF_2'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_55])).
% 2.76/1.53  tff(c_249, plain, (~m1_subset_1('#skF_2'(k2_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_247, c_105])).
% 2.76/1.53  tff(c_257, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_174, c_249])).
% 2.76/1.53  tff(c_260, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_77, c_257])).
% 2.76/1.53  tff(c_263, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_260])).
% 2.76/1.53  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_126, c_263])).
% 2.76/1.53  tff(c_268, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_55])).
% 2.76/1.53  tff(c_359, plain, (![A_103, B_104, C_105]: (k2_relset_1(A_103, B_104, C_105)=k2_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.76/1.53  tff(c_370, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_359])).
% 2.76/1.53  tff(c_374, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_268, c_370])).
% 2.76/1.53  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_374])).
% 2.76/1.53  tff(c_377, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_76])).
% 2.76/1.53  tff(c_565, plain, (![A_137, B_138, C_139]: (k1_relset_1(A_137, B_138, C_139)=k1_relat_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.76/1.53  tff(c_576, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_565])).
% 2.76/1.53  tff(c_580, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_377, c_576])).
% 2.76/1.53  tff(c_582, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_580])).
% 2.76/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.53  
% 2.76/1.53  Inference rules
% 2.76/1.53  ----------------------
% 2.76/1.53  #Ref     : 0
% 2.76/1.53  #Sup     : 107
% 2.76/1.53  #Fact    : 0
% 2.76/1.53  #Define  : 0
% 2.76/1.53  #Split   : 3
% 2.76/1.53  #Chain   : 0
% 2.76/1.53  #Close   : 0
% 2.76/1.53  
% 2.76/1.53  Ordering : KBO
% 2.76/1.53  
% 2.76/1.53  Simplification rules
% 2.76/1.53  ----------------------
% 2.76/1.53  #Subsume      : 3
% 2.76/1.53  #Demod        : 30
% 2.76/1.53  #Tautology    : 20
% 2.76/1.53  #SimpNegUnit  : 4
% 2.76/1.53  #BackRed      : 8
% 2.76/1.53  
% 2.76/1.53  #Partial instantiations: 0
% 2.76/1.53  #Strategies tried      : 1
% 2.76/1.53  
% 2.76/1.53  Timing (in seconds)
% 2.76/1.53  ----------------------
% 2.76/1.53  Preprocessing        : 0.41
% 2.76/1.53  Parsing              : 0.25
% 2.76/1.53  CNF conversion       : 0.02
% 2.76/1.53  Main loop            : 0.29
% 2.76/1.53  Inferencing          : 0.11
% 2.76/1.53  Reduction            : 0.08
% 2.76/1.53  Demodulation         : 0.05
% 2.76/1.53  BG Simplification    : 0.02
% 2.86/1.53  Subsumption          : 0.04
% 2.86/1.53  Abstraction          : 0.02
% 2.86/1.53  MUC search           : 0.00
% 2.86/1.53  Cooper               : 0.00
% 2.86/1.53  Total                : 0.73
% 2.86/1.53  Index Insertion      : 0.00
% 2.86/1.53  Index Deletion       : 0.00
% 2.86/1.53  Index Matching       : 0.00
% 2.86/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
