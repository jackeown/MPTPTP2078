%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:29 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 142 expanded)
%              Number of leaves         :   35 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  105 ( 274 expanded)
%              Number of equality atoms :   29 (  65 expanded)
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

tff(f_105,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_42,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_68,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_74,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_68])).

tff(c_78,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_74])).

tff(c_132,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_141,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_132])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) = k1_xboole_0
      | k2_relat_1(A_17) != k1_xboole_0
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_82,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78,c_26])).

tff(c_83,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_84,plain,(
    ! [A_54] :
      ( k2_relat_1(A_54) = k1_xboole_0
      | k1_relat_1(A_54) != k1_xboole_0
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_91,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78,c_84])).

tff(c_93,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_91])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_238,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_1'(A_90,B_91),B_91)
      | r2_hidden('#skF_2'(A_90,B_91),A_90)
      | B_91 = A_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_566,plain,(
    ! [A_133,B_134] :
      ( ~ r1_tarski(A_133,'#skF_2'(A_133,B_134))
      | r2_hidden('#skF_1'(A_133,B_134),B_134)
      | B_134 = A_133 ) ),
    inference(resolution,[status(thm)],[c_238,c_30])).

tff(c_575,plain,(
    ! [B_135] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_135),B_135)
      | k1_xboole_0 = B_135 ) ),
    inference(resolution,[status(thm)],[c_10,c_566])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_186,plain,(
    ! [A_75,C_76,B_77] :
      ( m1_subset_1(A_75,C_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(C_76))
      | ~ r2_hidden(A_75,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_191,plain,(
    ! [A_75,B_6,A_5] :
      ( m1_subset_1(A_75,B_6)
      | ~ r2_hidden(A_75,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_186])).

tff(c_647,plain,(
    ! [B_139,B_140] :
      ( m1_subset_1('#skF_1'(k1_xboole_0,B_139),B_140)
      | ~ r1_tarski(B_139,B_140)
      | k1_xboole_0 = B_139 ) ),
    inference(resolution,[status(thm)],[c_575,c_191])).

tff(c_473,plain,(
    ! [A_118,B_119,C_120] :
      ( k1_relset_1(A_118,B_119,C_120) = k1_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_482,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_473])).

tff(c_40,plain,(
    ! [D_40] :
      ( ~ r2_hidden(D_40,k1_relset_1('#skF_4','#skF_3','#skF_5'))
      | ~ m1_subset_1(D_40,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_485,plain,(
    ! [D_40] :
      ( ~ r2_hidden(D_40,k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_40,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_40])).

tff(c_583,plain,
    ( ~ m1_subset_1('#skF_1'(k1_xboole_0,k1_relat_1('#skF_5')),'#skF_4')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_575,c_485])).

tff(c_598,plain,(
    ~ m1_subset_1('#skF_1'(k1_xboole_0,k1_relat_1('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_583])).

tff(c_650,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_647,c_598])).

tff(c_680,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_650])).

tff(c_690,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_680])).

tff(c_694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_141,c_690])).

tff(c_696,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_956,plain,(
    ! [A_192,B_193,C_194] :
      ( k2_relset_1(A_192,B_193,C_194) = k2_relat_1(C_194)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_963,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_956])).

tff(c_966,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_963])).

tff(c_968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_966])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n012.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 11:45:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.43  
% 3.08/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.43  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.08/1.43  
% 3.08/1.43  %Foreground sorts:
% 3.08/1.43  
% 3.08/1.43  
% 3.08/1.43  %Background operators:
% 3.08/1.43  
% 3.08/1.43  
% 3.08/1.43  %Foreground operators:
% 3.08/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.08/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.08/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.08/1.43  tff('#skF_5', type, '#skF_5': $i).
% 3.08/1.43  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.08/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.08/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.08/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.08/1.43  tff('#skF_4', type, '#skF_4': $i).
% 3.08/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.08/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.08/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.08/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.08/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.08/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.43  
% 3.08/1.45  tff(f_105, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 3.08/1.45  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.08/1.45  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.08/1.45  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.08/1.45  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.08/1.45  tff(f_65, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.08/1.45  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.08/1.45  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 3.08/1.45  tff(f_70, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.08/1.45  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.08/1.45  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.08/1.45  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.08/1.45  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.08/1.45  tff(c_42, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.08/1.45  tff(c_24, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.08/1.45  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.08/1.45  tff(c_68, plain, (![B_52, A_53]: (v1_relat_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.08/1.45  tff(c_74, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_68])).
% 3.08/1.45  tff(c_78, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_74])).
% 3.08/1.45  tff(c_132, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.45  tff(c_141, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_132])).
% 3.08/1.45  tff(c_22, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(B_14), A_13) | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.08/1.45  tff(c_26, plain, (![A_17]: (k1_relat_1(A_17)=k1_xboole_0 | k2_relat_1(A_17)!=k1_xboole_0 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.08/1.45  tff(c_82, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_78, c_26])).
% 3.08/1.45  tff(c_83, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_82])).
% 3.08/1.45  tff(c_84, plain, (![A_54]: (k2_relat_1(A_54)=k1_xboole_0 | k1_relat_1(A_54)!=k1_xboole_0 | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.08/1.45  tff(c_91, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_78, c_84])).
% 3.08/1.45  tff(c_93, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_83, c_91])).
% 3.08/1.45  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.08/1.45  tff(c_238, plain, (![A_90, B_91]: (r2_hidden('#skF_1'(A_90, B_91), B_91) | r2_hidden('#skF_2'(A_90, B_91), A_90) | B_91=A_90)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.08/1.45  tff(c_30, plain, (![B_19, A_18]: (~r1_tarski(B_19, A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.08/1.45  tff(c_566, plain, (![A_133, B_134]: (~r1_tarski(A_133, '#skF_2'(A_133, B_134)) | r2_hidden('#skF_1'(A_133, B_134), B_134) | B_134=A_133)), inference(resolution, [status(thm)], [c_238, c_30])).
% 3.08/1.45  tff(c_575, plain, (![B_135]: (r2_hidden('#skF_1'(k1_xboole_0, B_135), B_135) | k1_xboole_0=B_135)), inference(resolution, [status(thm)], [c_10, c_566])).
% 3.08/1.45  tff(c_14, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.08/1.45  tff(c_186, plain, (![A_75, C_76, B_77]: (m1_subset_1(A_75, C_76) | ~m1_subset_1(B_77, k1_zfmisc_1(C_76)) | ~r2_hidden(A_75, B_77))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.08/1.45  tff(c_191, plain, (![A_75, B_6, A_5]: (m1_subset_1(A_75, B_6) | ~r2_hidden(A_75, A_5) | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_14, c_186])).
% 3.08/1.45  tff(c_647, plain, (![B_139, B_140]: (m1_subset_1('#skF_1'(k1_xboole_0, B_139), B_140) | ~r1_tarski(B_139, B_140) | k1_xboole_0=B_139)), inference(resolution, [status(thm)], [c_575, c_191])).
% 3.08/1.45  tff(c_473, plain, (![A_118, B_119, C_120]: (k1_relset_1(A_118, B_119, C_120)=k1_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.08/1.45  tff(c_482, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_473])).
% 3.08/1.45  tff(c_40, plain, (![D_40]: (~r2_hidden(D_40, k1_relset_1('#skF_4', '#skF_3', '#skF_5')) | ~m1_subset_1(D_40, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.08/1.45  tff(c_485, plain, (![D_40]: (~r2_hidden(D_40, k1_relat_1('#skF_5')) | ~m1_subset_1(D_40, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_482, c_40])).
% 3.08/1.45  tff(c_583, plain, (~m1_subset_1('#skF_1'(k1_xboole_0, k1_relat_1('#skF_5')), '#skF_4') | k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_575, c_485])).
% 3.08/1.45  tff(c_598, plain, (~m1_subset_1('#skF_1'(k1_xboole_0, k1_relat_1('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_93, c_583])).
% 3.08/1.45  tff(c_650, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_647, c_598])).
% 3.08/1.45  tff(c_680, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_93, c_650])).
% 3.08/1.45  tff(c_690, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_680])).
% 3.08/1.45  tff(c_694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_141, c_690])).
% 3.08/1.45  tff(c_696, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_82])).
% 3.08/1.45  tff(c_956, plain, (![A_192, B_193, C_194]: (k2_relset_1(A_192, B_193, C_194)=k2_relat_1(C_194) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.08/1.45  tff(c_963, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_956])).
% 3.08/1.45  tff(c_966, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_696, c_963])).
% 3.08/1.45  tff(c_968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_966])).
% 3.08/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.45  
% 3.08/1.45  Inference rules
% 3.08/1.45  ----------------------
% 3.08/1.45  #Ref     : 0
% 3.08/1.45  #Sup     : 170
% 3.08/1.45  #Fact    : 0
% 3.08/1.45  #Define  : 0
% 3.08/1.45  #Split   : 13
% 3.08/1.45  #Chain   : 0
% 3.08/1.45  #Close   : 0
% 3.08/1.45  
% 3.08/1.45  Ordering : KBO
% 3.08/1.45  
% 3.08/1.45  Simplification rules
% 3.08/1.45  ----------------------
% 3.08/1.45  #Subsume      : 46
% 3.08/1.45  #Demod        : 56
% 3.08/1.45  #Tautology    : 52
% 3.08/1.45  #SimpNegUnit  : 45
% 3.08/1.45  #BackRed      : 24
% 3.08/1.45  
% 3.08/1.45  #Partial instantiations: 0
% 3.08/1.45  #Strategies tried      : 1
% 3.08/1.45  
% 3.08/1.45  Timing (in seconds)
% 3.08/1.45  ----------------------
% 3.08/1.45  Preprocessing        : 0.31
% 3.08/1.45  Parsing              : 0.17
% 3.08/1.45  CNF conversion       : 0.02
% 3.08/1.45  Main loop            : 0.38
% 3.08/1.45  Inferencing          : 0.15
% 3.08/1.45  Reduction            : 0.11
% 3.08/1.45  Demodulation         : 0.07
% 3.08/1.45  BG Simplification    : 0.02
% 3.08/1.45  Subsumption          : 0.06
% 3.08/1.45  Abstraction          : 0.02
% 3.08/1.45  MUC search           : 0.00
% 3.08/1.45  Cooper               : 0.00
% 3.08/1.45  Total                : 0.72
% 3.08/1.45  Index Insertion      : 0.00
% 3.08/1.45  Index Deletion       : 0.00
% 3.08/1.45  Index Matching       : 0.00
% 3.08/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
