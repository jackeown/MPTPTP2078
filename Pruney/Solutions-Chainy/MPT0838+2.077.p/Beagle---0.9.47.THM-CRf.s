%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:20 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 118 expanded)
%              Number of leaves         :   35 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 220 expanded)
%              Number of equality atoms :   24 (  49 expanded)
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

tff(f_76,axiom,(
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

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_42,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_68,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_74,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_68])).

tff(c_78,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_74])).

tff(c_142,plain,(
    ! [C_64,B_65,A_66] :
      ( v5_relat_1(C_64,B_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_151,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_142])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
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

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_295,plain,(
    ! [A_101,B_102] :
      ( r2_hidden('#skF_1'(A_101,B_102),B_102)
      | r2_hidden('#skF_2'(A_101,B_102),A_101)
      | B_102 = A_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_587,plain,(
    ! [A_139,B_140] :
      ( ~ r1_tarski(A_139,'#skF_2'(A_139,B_140))
      | r2_hidden('#skF_1'(A_139,B_140),B_140)
      | B_140 = A_139 ) ),
    inference(resolution,[status(thm)],[c_295,c_30])).

tff(c_596,plain,(
    ! [B_141] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_141),B_141)
      | k1_xboole_0 = B_141 ) ),
    inference(resolution,[status(thm)],[c_10,c_587])).

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

tff(c_656,plain,(
    ! [B_144,B_145] :
      ( m1_subset_1('#skF_1'(k1_xboole_0,B_144),B_145)
      | ~ r1_tarski(B_144,B_145)
      | k1_xboole_0 = B_144 ) ),
    inference(resolution,[status(thm)],[c_596,c_191])).

tff(c_501,plain,(
    ! [A_125,B_126,C_127] :
      ( k2_relset_1(A_125,B_126,C_127) = k2_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_510,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_501])).

tff(c_40,plain,(
    ! [D_40] :
      ( ~ r2_hidden(D_40,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_40,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_513,plain,(
    ! [D_40] :
      ( ~ r2_hidden(D_40,k2_relat_1('#skF_5'))
      | ~ m1_subset_1(D_40,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_40])).

tff(c_607,plain,
    ( ~ m1_subset_1('#skF_1'(k1_xboole_0,k2_relat_1('#skF_5')),'#skF_4')
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_596,c_513])).

tff(c_621,plain,(
    ~ m1_subset_1('#skF_1'(k1_xboole_0,k2_relat_1('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_607])).

tff(c_659,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_656,c_621])).

tff(c_689,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_659])).

tff(c_699,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_689])).

tff(c_703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_151,c_699])).

tff(c_704,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_1029,plain,(
    ! [A_205,B_206,C_207] :
      ( k1_relset_1(A_205,B_206,C_207) = k1_relat_1(C_207)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1036,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_1029])).

tff(c_1039,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_1036])).

tff(c_1041,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1039])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:35:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.48  
% 3.28/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.48  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.28/1.48  
% 3.28/1.48  %Foreground sorts:
% 3.28/1.48  
% 3.28/1.48  
% 3.28/1.48  %Background operators:
% 3.28/1.48  
% 3.28/1.48  
% 3.28/1.48  %Foreground operators:
% 3.28/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.28/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.28/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.28/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.28/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.28/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.28/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.28/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.28/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.28/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.28/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.48  
% 3.28/1.50  tff(f_105, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.28/1.50  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.28/1.50  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.28/1.50  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.28/1.50  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.28/1.50  tff(f_65, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.28/1.50  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.28/1.50  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.28/1.50  tff(f_70, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.28/1.50  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.28/1.50  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.28/1.50  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.28/1.50  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.28/1.50  tff(c_42, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.28/1.50  tff(c_24, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.28/1.50  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.28/1.50  tff(c_68, plain, (![B_52, A_53]: (v1_relat_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.28/1.50  tff(c_74, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_68])).
% 3.28/1.50  tff(c_78, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_74])).
% 3.28/1.50  tff(c_142, plain, (![C_64, B_65, A_66]: (v5_relat_1(C_64, B_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.28/1.50  tff(c_151, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_142])).
% 3.28/1.50  tff(c_22, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.28/1.50  tff(c_26, plain, (![A_17]: (k1_relat_1(A_17)=k1_xboole_0 | k2_relat_1(A_17)!=k1_xboole_0 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.28/1.50  tff(c_82, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_78, c_26])).
% 3.28/1.50  tff(c_83, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_82])).
% 3.28/1.50  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.28/1.50  tff(c_295, plain, (![A_101, B_102]: (r2_hidden('#skF_1'(A_101, B_102), B_102) | r2_hidden('#skF_2'(A_101, B_102), A_101) | B_102=A_101)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.28/1.50  tff(c_30, plain, (![B_19, A_18]: (~r1_tarski(B_19, A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.28/1.50  tff(c_587, plain, (![A_139, B_140]: (~r1_tarski(A_139, '#skF_2'(A_139, B_140)) | r2_hidden('#skF_1'(A_139, B_140), B_140) | B_140=A_139)), inference(resolution, [status(thm)], [c_295, c_30])).
% 3.28/1.50  tff(c_596, plain, (![B_141]: (r2_hidden('#skF_1'(k1_xboole_0, B_141), B_141) | k1_xboole_0=B_141)), inference(resolution, [status(thm)], [c_10, c_587])).
% 3.28/1.50  tff(c_14, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.28/1.50  tff(c_186, plain, (![A_75, C_76, B_77]: (m1_subset_1(A_75, C_76) | ~m1_subset_1(B_77, k1_zfmisc_1(C_76)) | ~r2_hidden(A_75, B_77))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.28/1.50  tff(c_191, plain, (![A_75, B_6, A_5]: (m1_subset_1(A_75, B_6) | ~r2_hidden(A_75, A_5) | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_14, c_186])).
% 3.28/1.50  tff(c_656, plain, (![B_144, B_145]: (m1_subset_1('#skF_1'(k1_xboole_0, B_144), B_145) | ~r1_tarski(B_144, B_145) | k1_xboole_0=B_144)), inference(resolution, [status(thm)], [c_596, c_191])).
% 3.28/1.50  tff(c_501, plain, (![A_125, B_126, C_127]: (k2_relset_1(A_125, B_126, C_127)=k2_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.28/1.50  tff(c_510, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_501])).
% 3.28/1.50  tff(c_40, plain, (![D_40]: (~r2_hidden(D_40, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_40, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.28/1.50  tff(c_513, plain, (![D_40]: (~r2_hidden(D_40, k2_relat_1('#skF_5')) | ~m1_subset_1(D_40, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_510, c_40])).
% 3.28/1.50  tff(c_607, plain, (~m1_subset_1('#skF_1'(k1_xboole_0, k2_relat_1('#skF_5')), '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_596, c_513])).
% 3.28/1.50  tff(c_621, plain, (~m1_subset_1('#skF_1'(k1_xboole_0, k2_relat_1('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_83, c_607])).
% 3.28/1.50  tff(c_659, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_656, c_621])).
% 3.28/1.50  tff(c_689, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_83, c_659])).
% 3.28/1.50  tff(c_699, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_689])).
% 3.28/1.50  tff(c_703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_151, c_699])).
% 3.28/1.50  tff(c_704, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_82])).
% 3.28/1.50  tff(c_1029, plain, (![A_205, B_206, C_207]: (k1_relset_1(A_205, B_206, C_207)=k1_relat_1(C_207) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.28/1.50  tff(c_1036, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_1029])).
% 3.28/1.50  tff(c_1039, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_704, c_1036])).
% 3.28/1.50  tff(c_1041, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_1039])).
% 3.28/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.50  
% 3.28/1.50  Inference rules
% 3.28/1.50  ----------------------
% 3.28/1.50  #Ref     : 0
% 3.28/1.50  #Sup     : 180
% 3.28/1.50  #Fact    : 0
% 3.28/1.50  #Define  : 0
% 3.28/1.50  #Split   : 15
% 3.28/1.50  #Chain   : 0
% 3.28/1.50  #Close   : 0
% 3.28/1.50  
% 3.28/1.50  Ordering : KBO
% 3.28/1.50  
% 3.28/1.50  Simplification rules
% 3.28/1.50  ----------------------
% 3.28/1.50  #Subsume      : 52
% 3.28/1.50  #Demod        : 78
% 3.28/1.50  #Tautology    : 52
% 3.28/1.50  #SimpNegUnit  : 52
% 3.28/1.50  #BackRed      : 29
% 3.28/1.50  
% 3.28/1.50  #Partial instantiations: 0
% 3.28/1.50  #Strategies tried      : 1
% 3.28/1.50  
% 3.28/1.50  Timing (in seconds)
% 3.28/1.50  ----------------------
% 3.37/1.50  Preprocessing        : 0.31
% 3.37/1.50  Parsing              : 0.17
% 3.37/1.50  CNF conversion       : 0.02
% 3.37/1.50  Main loop            : 0.41
% 3.37/1.50  Inferencing          : 0.16
% 3.37/1.50  Reduction            : 0.12
% 3.37/1.50  Demodulation         : 0.08
% 3.37/1.50  BG Simplification    : 0.02
% 3.37/1.50  Subsumption          : 0.07
% 3.37/1.50  Abstraction          : 0.02
% 3.37/1.50  MUC search           : 0.00
% 3.37/1.50  Cooper               : 0.00
% 3.37/1.50  Total                : 0.75
% 3.37/1.50  Index Insertion      : 0.00
% 3.37/1.50  Index Deletion       : 0.00
% 3.37/1.50  Index Matching       : 0.00
% 3.37/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
