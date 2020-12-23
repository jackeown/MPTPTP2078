%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:11 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 124 expanded)
%              Number of leaves         :   34 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 234 expanded)
%              Number of equality atoms :   32 (  71 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_102,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
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

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_44,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_93,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_106,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_93])).

tff(c_171,plain,(
    ! [C_67,B_68,A_69] :
      ( v5_relat_1(C_67,B_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_186,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_171])).

tff(c_26,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [A_15] :
      ( k2_relat_1(A_15) = k1_xboole_0
      | k1_relat_1(A_15) != k1_xboole_0
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_114,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_106,c_30])).

tff(c_123,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_28,plain,(
    ! [A_15] :
      ( k1_relat_1(A_15) = k1_xboole_0
      | k2_relat_1(A_15) != k1_xboole_0
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_115,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_106,c_28])).

tff(c_124,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_115])).

tff(c_306,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_1'(A_104,B_105),B_105)
      | r2_hidden('#skF_2'(A_104,B_105),A_104)
      | B_105 = A_104 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_73,plain,(
    ! [A_42,B_43] : ~ r2_hidden(A_42,k2_zfmisc_1(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_76,plain,(
    ! [A_4] : ~ r2_hidden(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_73])).

tff(c_330,plain,(
    ! [B_106] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_106),B_106)
      | k1_xboole_0 = B_106 ) ),
    inference(resolution,[status(thm)],[c_306,c_76])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_226,plain,(
    ! [A_80,C_81,B_82] :
      ( m1_subset_1(A_80,C_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(C_81))
      | ~ r2_hidden(A_80,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_231,plain,(
    ! [A_80,B_9,A_8] :
      ( m1_subset_1(A_80,B_9)
      | ~ r2_hidden(A_80,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_20,c_226])).

tff(c_425,plain,(
    ! [B_127,B_128] :
      ( m1_subset_1('#skF_1'(k1_xboole_0,B_127),B_128)
      | ~ r1_tarski(B_127,B_128)
      | k1_xboole_0 = B_127 ) ),
    inference(resolution,[status(thm)],[c_330,c_231])).

tff(c_275,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_290,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_275])).

tff(c_42,plain,(
    ! [D_39] :
      ( ~ r2_hidden(D_39,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_39,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_291,plain,(
    ! [D_39] :
      ( ~ r2_hidden(D_39,k2_relat_1('#skF_5'))
      | ~ m1_subset_1(D_39,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_42])).

tff(c_334,plain,
    ( ~ m1_subset_1('#skF_1'(k1_xboole_0,k2_relat_1('#skF_5')),'#skF_4')
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_330,c_291])).

tff(c_343,plain,(
    ~ m1_subset_1('#skF_1'(k1_xboole_0,k2_relat_1('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_334])).

tff(c_444,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_425,c_343])).

tff(c_485,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_444])).

tff(c_511,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_485])).

tff(c_515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_186,c_511])).

tff(c_517,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_1016,plain,(
    ! [A_211,B_212,C_213] :
      ( k1_relset_1(A_211,B_212,C_213) = k1_relat_1(C_213)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1027,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_1016])).

tff(c_1037,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_1027])).

tff(c_1039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1037])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.47  
% 3.05/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.47  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.05/1.47  
% 3.05/1.47  %Foreground sorts:
% 3.05/1.47  
% 3.05/1.47  
% 3.05/1.47  %Background operators:
% 3.05/1.47  
% 3.05/1.47  
% 3.05/1.47  %Foreground operators:
% 3.05/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.05/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.05/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.05/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.05/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.05/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.05/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.05/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.05/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.05/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.05/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.05/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.05/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.05/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.05/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.47  
% 3.05/1.48  tff(f_102, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.05/1.48  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.05/1.48  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.05/1.48  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.05/1.48  tff(f_63, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.05/1.48  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.05/1.48  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.05/1.48  tff(f_41, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.05/1.48  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.05/1.48  tff(f_51, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.05/1.48  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.05/1.48  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.05/1.48  tff(c_44, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.05/1.48  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.05/1.48  tff(c_93, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.05/1.48  tff(c_106, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_93])).
% 3.05/1.48  tff(c_171, plain, (![C_67, B_68, A_69]: (v5_relat_1(C_67, B_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.05/1.48  tff(c_186, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_171])).
% 3.05/1.48  tff(c_26, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.05/1.48  tff(c_30, plain, (![A_15]: (k2_relat_1(A_15)=k1_xboole_0 | k1_relat_1(A_15)!=k1_xboole_0 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.05/1.48  tff(c_114, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_106, c_30])).
% 3.05/1.48  tff(c_123, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_114])).
% 3.05/1.48  tff(c_28, plain, (![A_15]: (k1_relat_1(A_15)=k1_xboole_0 | k2_relat_1(A_15)!=k1_xboole_0 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.05/1.48  tff(c_115, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_106, c_28])).
% 3.05/1.48  tff(c_124, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_123, c_115])).
% 3.05/1.48  tff(c_306, plain, (![A_104, B_105]: (r2_hidden('#skF_1'(A_104, B_105), B_105) | r2_hidden('#skF_2'(A_104, B_105), A_104) | B_105=A_104)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.05/1.48  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.05/1.48  tff(c_73, plain, (![A_42, B_43]: (~r2_hidden(A_42, k2_zfmisc_1(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.05/1.48  tff(c_76, plain, (![A_4]: (~r2_hidden(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_73])).
% 3.05/1.48  tff(c_330, plain, (![B_106]: (r2_hidden('#skF_1'(k1_xboole_0, B_106), B_106) | k1_xboole_0=B_106)), inference(resolution, [status(thm)], [c_306, c_76])).
% 3.05/1.48  tff(c_20, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.05/1.48  tff(c_226, plain, (![A_80, C_81, B_82]: (m1_subset_1(A_80, C_81) | ~m1_subset_1(B_82, k1_zfmisc_1(C_81)) | ~r2_hidden(A_80, B_82))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.05/1.48  tff(c_231, plain, (![A_80, B_9, A_8]: (m1_subset_1(A_80, B_9) | ~r2_hidden(A_80, A_8) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_20, c_226])).
% 3.05/1.48  tff(c_425, plain, (![B_127, B_128]: (m1_subset_1('#skF_1'(k1_xboole_0, B_127), B_128) | ~r1_tarski(B_127, B_128) | k1_xboole_0=B_127)), inference(resolution, [status(thm)], [c_330, c_231])).
% 3.05/1.48  tff(c_275, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.05/1.48  tff(c_290, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_275])).
% 3.05/1.48  tff(c_42, plain, (![D_39]: (~r2_hidden(D_39, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_39, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.05/1.48  tff(c_291, plain, (![D_39]: (~r2_hidden(D_39, k2_relat_1('#skF_5')) | ~m1_subset_1(D_39, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_290, c_42])).
% 3.05/1.48  tff(c_334, plain, (~m1_subset_1('#skF_1'(k1_xboole_0, k2_relat_1('#skF_5')), '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_330, c_291])).
% 3.05/1.48  tff(c_343, plain, (~m1_subset_1('#skF_1'(k1_xboole_0, k2_relat_1('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_124, c_334])).
% 3.05/1.48  tff(c_444, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_425, c_343])).
% 3.05/1.48  tff(c_485, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_124, c_444])).
% 3.05/1.48  tff(c_511, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_485])).
% 3.05/1.48  tff(c_515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_186, c_511])).
% 3.05/1.48  tff(c_517, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_114])).
% 3.05/1.48  tff(c_1016, plain, (![A_211, B_212, C_213]: (k1_relset_1(A_211, B_212, C_213)=k1_relat_1(C_213) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.05/1.48  tff(c_1027, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_1016])).
% 3.05/1.48  tff(c_1037, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_517, c_1027])).
% 3.05/1.48  tff(c_1039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1037])).
% 3.05/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.48  
% 3.05/1.48  Inference rules
% 3.05/1.48  ----------------------
% 3.05/1.48  #Ref     : 0
% 3.05/1.48  #Sup     : 214
% 3.05/1.48  #Fact    : 0
% 3.05/1.48  #Define  : 0
% 3.05/1.48  #Split   : 5
% 3.05/1.48  #Chain   : 0
% 3.05/1.48  #Close   : 0
% 3.05/1.48  
% 3.05/1.48  Ordering : KBO
% 3.05/1.48  
% 3.05/1.48  Simplification rules
% 3.05/1.48  ----------------------
% 3.05/1.48  #Subsume      : 42
% 3.05/1.48  #Demod        : 29
% 3.05/1.48  #Tautology    : 34
% 3.05/1.48  #SimpNegUnit  : 5
% 3.05/1.48  #BackRed      : 2
% 3.05/1.48  
% 3.05/1.48  #Partial instantiations: 0
% 3.05/1.48  #Strategies tried      : 1
% 3.05/1.48  
% 3.05/1.48  Timing (in seconds)
% 3.05/1.48  ----------------------
% 3.26/1.49  Preprocessing        : 0.30
% 3.26/1.49  Parsing              : 0.16
% 3.26/1.49  CNF conversion       : 0.02
% 3.26/1.49  Main loop            : 0.39
% 3.26/1.49  Inferencing          : 0.16
% 3.26/1.49  Reduction            : 0.10
% 3.26/1.49  Demodulation         : 0.06
% 3.26/1.49  BG Simplification    : 0.02
% 3.26/1.49  Subsumption          : 0.06
% 3.26/1.49  Abstraction          : 0.02
% 3.26/1.49  MUC search           : 0.00
% 3.26/1.49  Cooper               : 0.00
% 3.26/1.49  Total                : 0.72
% 3.26/1.49  Index Insertion      : 0.00
% 3.26/1.49  Index Deletion       : 0.00
% 3.26/1.49  Index Matching       : 0.00
% 3.26/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
