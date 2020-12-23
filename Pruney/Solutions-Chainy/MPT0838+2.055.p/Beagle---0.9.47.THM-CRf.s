%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:17 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 107 expanded)
%              Number of leaves         :   34 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 198 expanded)
%              Number of equality atoms :   23 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_42,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_26,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_63,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_69,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_63])).

tff(c_73,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_69])).

tff(c_95,plain,(
    ! [C_57,B_58,A_59] :
      ( v5_relat_1(C_57,B_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_104,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_95])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k2_relat_1(B_15),A_14)
      | ~ v5_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_52,plain,(
    ! [C_46,A_47] :
      ( r2_hidden(C_46,k1_zfmisc_1(A_47))
      | ~ r1_tarski(C_46,A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_60,plain,(
    ! [C_46,A_47] :
      ( m1_subset_1(C_46,k1_zfmisc_1(A_47))
      | ~ r1_tarski(C_46,A_47) ) ),
    inference(resolution,[status(thm)],[c_52,c_18])).

tff(c_75,plain,(
    ! [A_55] :
      ( k1_relat_1(A_55) = k1_xboole_0
      | k2_relat_1(A_55) != k1_xboole_0
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_82,plain,
    ( k1_relat_1('#skF_6') = k1_xboole_0
    | k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_75])).

tff(c_84,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1('#skF_3'(A_6,B_7),A_6)
      | k1_xboole_0 = B_7
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7),B_7)
      | k1_xboole_0 = B_7
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_249,plain,(
    ! [A_97,B_98,C_99] :
      ( k2_relset_1(A_97,B_98,C_99) = k2_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_268,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_249])).

tff(c_40,plain,(
    ! [D_39] :
      ( ~ r2_hidden(D_39,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(D_39,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_274,plain,(
    ! [D_100] :
      ( ~ r2_hidden(D_100,k2_relat_1('#skF_6'))
      | ~ m1_subset_1(D_100,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_40])).

tff(c_278,plain,(
    ! [A_6] :
      ( ~ m1_subset_1('#skF_3'(A_6,k2_relat_1('#skF_6')),'#skF_5')
      | k2_relat_1('#skF_6') = k1_xboole_0
      | ~ m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(A_6)) ) ),
    inference(resolution,[status(thm)],[c_14,c_274])).

tff(c_288,plain,(
    ! [A_104] :
      ( ~ m1_subset_1('#skF_3'(A_104,k2_relat_1('#skF_6')),'#skF_5')
      | ~ m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(A_104)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_278])).

tff(c_292,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | ~ m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_16,c_288])).

tff(c_295,plain,(
    ~ m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_292])).

tff(c_314,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_295])).

tff(c_317,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_314])).

tff(c_321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_104,c_317])).

tff(c_322,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_534,plain,(
    ! [A_147,B_148,C_149] :
      ( k1_relset_1(A_147,B_148,C_149) = k1_relat_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_549,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_534])).

tff(c_554,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_549])).

tff(c_556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_554])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:27:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.31  
% 2.38/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.32  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 2.38/1.32  
% 2.38/1.32  %Foreground sorts:
% 2.38/1.32  
% 2.38/1.32  
% 2.38/1.32  %Background operators:
% 2.38/1.32  
% 2.38/1.32  
% 2.38/1.32  %Foreground operators:
% 2.38/1.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.38/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.38/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.38/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.38/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.38/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.38/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.38/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.38/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.38/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.38/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.38/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.38/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.38/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.38/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.32  
% 2.38/1.33  tff(f_104, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 2.38/1.33  tff(f_63, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.38/1.33  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.38/1.33  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.38/1.33  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.38/1.33  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.38/1.33  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.38/1.33  tff(f_69, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.38/1.33  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 2.38/1.33  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.38/1.33  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.38/1.33  tff(c_42, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.38/1.33  tff(c_26, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.38/1.33  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.38/1.33  tff(c_63, plain, (![B_51, A_52]: (v1_relat_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.38/1.33  tff(c_69, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_63])).
% 2.38/1.33  tff(c_73, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_69])).
% 2.38/1.33  tff(c_95, plain, (![C_57, B_58, A_59]: (v5_relat_1(C_57, B_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.38/1.33  tff(c_104, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_95])).
% 2.38/1.33  tff(c_24, plain, (![B_15, A_14]: (r1_tarski(k2_relat_1(B_15), A_14) | ~v5_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.38/1.33  tff(c_52, plain, (![C_46, A_47]: (r2_hidden(C_46, k1_zfmisc_1(A_47)) | ~r1_tarski(C_46, A_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.38/1.33  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.38/1.33  tff(c_60, plain, (![C_46, A_47]: (m1_subset_1(C_46, k1_zfmisc_1(A_47)) | ~r1_tarski(C_46, A_47))), inference(resolution, [status(thm)], [c_52, c_18])).
% 2.38/1.33  tff(c_75, plain, (![A_55]: (k1_relat_1(A_55)=k1_xboole_0 | k2_relat_1(A_55)!=k1_xboole_0 | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.38/1.33  tff(c_82, plain, (k1_relat_1('#skF_6')=k1_xboole_0 | k2_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_73, c_75])).
% 2.38/1.33  tff(c_84, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_82])).
% 2.38/1.33  tff(c_16, plain, (![A_6, B_7]: (m1_subset_1('#skF_3'(A_6, B_7), A_6) | k1_xboole_0=B_7 | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.38/1.33  tff(c_14, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7), B_7) | k1_xboole_0=B_7 | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.38/1.33  tff(c_249, plain, (![A_97, B_98, C_99]: (k2_relset_1(A_97, B_98, C_99)=k2_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.38/1.33  tff(c_268, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_249])).
% 2.38/1.33  tff(c_40, plain, (![D_39]: (~r2_hidden(D_39, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(D_39, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.38/1.33  tff(c_274, plain, (![D_100]: (~r2_hidden(D_100, k2_relat_1('#skF_6')) | ~m1_subset_1(D_100, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_40])).
% 2.38/1.33  tff(c_278, plain, (![A_6]: (~m1_subset_1('#skF_3'(A_6, k2_relat_1('#skF_6')), '#skF_5') | k2_relat_1('#skF_6')=k1_xboole_0 | ~m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(A_6)))), inference(resolution, [status(thm)], [c_14, c_274])).
% 2.38/1.33  tff(c_288, plain, (![A_104]: (~m1_subset_1('#skF_3'(A_104, k2_relat_1('#skF_6')), '#skF_5') | ~m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(A_104)))), inference(negUnitSimplification, [status(thm)], [c_84, c_278])).
% 2.38/1.33  tff(c_292, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | ~m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_288])).
% 2.38/1.33  tff(c_295, plain, (~m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_84, c_292])).
% 2.38/1.33  tff(c_314, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_60, c_295])).
% 2.38/1.33  tff(c_317, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_24, c_314])).
% 2.38/1.33  tff(c_321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_104, c_317])).
% 2.38/1.33  tff(c_322, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_82])).
% 2.38/1.33  tff(c_534, plain, (![A_147, B_148, C_149]: (k1_relset_1(A_147, B_148, C_149)=k1_relat_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.38/1.33  tff(c_549, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_534])).
% 2.38/1.33  tff(c_554, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_322, c_549])).
% 2.38/1.33  tff(c_556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_554])).
% 2.38/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.33  
% 2.38/1.33  Inference rules
% 2.38/1.33  ----------------------
% 2.38/1.33  #Ref     : 0
% 2.38/1.33  #Sup     : 99
% 2.38/1.33  #Fact    : 0
% 2.38/1.33  #Define  : 0
% 2.38/1.33  #Split   : 5
% 2.38/1.33  #Chain   : 0
% 2.38/1.33  #Close   : 0
% 2.38/1.33  
% 2.38/1.33  Ordering : KBO
% 2.38/1.33  
% 2.38/1.33  Simplification rules
% 2.38/1.33  ----------------------
% 2.38/1.33  #Subsume      : 5
% 2.38/1.33  #Demod        : 25
% 2.38/1.33  #Tautology    : 21
% 2.38/1.33  #SimpNegUnit  : 4
% 2.38/1.33  #BackRed      : 3
% 2.38/1.33  
% 2.38/1.33  #Partial instantiations: 0
% 2.38/1.33  #Strategies tried      : 1
% 2.38/1.33  
% 2.38/1.33  Timing (in seconds)
% 2.38/1.33  ----------------------
% 2.38/1.33  Preprocessing        : 0.31
% 2.38/1.33  Parsing              : 0.16
% 2.38/1.33  CNF conversion       : 0.02
% 2.38/1.33  Main loop            : 0.27
% 2.38/1.33  Inferencing          : 0.11
% 2.38/1.33  Reduction            : 0.07
% 2.38/1.33  Demodulation         : 0.05
% 2.38/1.33  BG Simplification    : 0.02
% 2.38/1.33  Subsumption          : 0.04
% 2.38/1.33  Abstraction          : 0.02
% 2.38/1.33  MUC search           : 0.00
% 2.38/1.33  Cooper               : 0.00
% 2.38/1.33  Total                : 0.61
% 2.38/1.34  Index Insertion      : 0.00
% 2.38/1.34  Index Deletion       : 0.00
% 2.38/1.34  Index Matching       : 0.00
% 2.38/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
